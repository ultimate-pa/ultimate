package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Applies the "memloc-array transformation"
 * Performs the following steps:
 * <ul>
 *  <li> introduce a fresh array-type variable, called the memloc-array
 *  <li> at each write to an array in the program, at location l with index variable i:
 *   <ul>
 *    <li> introduce a fresh memloc-literal "(l, i)" that represents this write location
 *    <li> update the memloc array like this: memloc[i] := (l,i);
 *   </ul>
 *  <li> make sure that all memloc-literals are assumed as distinct by the solver (may be done outside this class)
 * </ul>
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class MemlocArrayUpdaterIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {


	private final Map<StoreIndexInfo, IProgramConst> mStoreIndexInfoToLocLiteral;

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;

	private final static boolean TRACK_CONSTANTS = false;
	private final Set<ConstantTerm> mAllConstantTerms;


	private final IProgramVar mMemlocArrayInt;

	private final Sort mMemLocSort;

	private int mMemLocLitCounter = 0;

	private final List<IProgramVarOrConst> mHeapArrays;

	public MemlocArrayUpdaterIcfgTransformer(final ILogger logger, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final IProgramVar memlocArrayInt, final Sort memLocSort, final List<IProgramVarOrConst> heapArrays,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo) {
		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
		mAllConstantTerms = TRACK_CONSTANTS ? new HashSet<>() : null;
		mMemlocArrayInt = memlocArrayInt;
		mMemLocSort = memLocSort;
		mStoreIndexInfoToLocLiteral = new HashMap<>();
		mHeapArrays = heapArrays;
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		final UnmodifiableTransFormula newTransformula = transformTransformula(oldTransition.getTransformula(),
				new EdgeInfo(oldTransition));
		return super.transform(oldTransition, newSource, newTarget, newTransformula);
	}

	public final UnmodifiableTransFormula transformTransformula(final UnmodifiableTransFormula tf,
			final EdgeInfo edgeInfo) {

		if (TRACK_CONSTANTS) {
			/* update the all constants tracking */
			mAllConstantTerms.addAll(new SubTermFinder(t -> t instanceof ConstantTerm)
					.findMatchingSubterms(tf.getFormula())
					.stream().map(t -> (ConstantTerm) t)
					.collect(Collectors.toList()));
		}

		if (mEdgeToIndexToStoreIndexInfo.get(edgeInfo) == null) {
			// edge does not have any array writes --> return it unchanged
			return tf;
		}

		/*
		 * core business from here on..
		 */

		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();
		final Set<IProgramConst> extraConstants = new HashSet<>();

		mMgdScript.lock(this);

		final Map<Term, Term> memlocUpdates = new HashMap<>();

		for (final Entry<Term, StoreIndexInfo> en : mEdgeToIndexToStoreIndexInfo.get(edgeInfo).entrySet()) {

			final StoreIndexInfo storeIndexInfo = en.getValue();

			final Term indexTerm = storeIndexInfo.getIndexTerm();

			final IProgramConst locLit = getLocationLiteral(storeIndexInfo);
			extraConstants.add(locLit);

			/*
			 * updated the memloc array
			 *  in Boogie we would add memloc_int[indexTerm] := locLit
			 *  note that just adding the conjunct "memloc_int' = (store memloc_int indexTerm locLit)" is wrong here,
			 *   because if we add several of these constraints (always with the same in/outvar), then the overall
			 *    constraint has a much narrower meaning than intended!
			 *    (describing this because the first implementation did it wrong..)
			 */
			memlocUpdates.put(indexTerm, locLit.getTerm());
		}

		// construct a store chain for the memlocUpdates
		final Term memlocUpdateConjunct;// = mMgdScript.term(this, "true");
		{
			final TermVariable memlocIntInVar;
			final TermVariable memlocIntOutVar;
			assert !extraOutVars.containsKey(mMemlocArrayInt);
			memlocIntInVar = mMgdScript.constructFreshCopy(mMemlocArrayInt.getTermVariable());
			memlocIntOutVar = mMgdScript.constructFreshCopy(mMemlocArrayInt.getTermVariable());
			extraInVars.put(mMemlocArrayInt, memlocIntInVar);
			extraOutVars.put(mMemlocArrayInt, memlocIntOutVar);

			Term storeChain = memlocIntInVar;
			for (final Entry<Term, Term> en : memlocUpdates.entrySet()) {
				storeChain = SmtUtils.store(mMgdScript.getScript(), storeChain, en.getKey(), en.getValue());
			}
			memlocUpdateConjunct = SmtUtils.binaryEquality(mMgdScript.getScript(), memlocIntOutVar, storeChain);
		}

		mMgdScript.unlock(this);

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		newInVars.putAll(extraInVars);

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		newOutVars.putAll(extraOutVars);

		final Set<IProgramConst> newNonTheoryConsts = new HashSet<>(tf.getNonTheoryConsts());
		newNonTheoryConsts.addAll(extraConstants);

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars,
				newNonTheoryConsts.isEmpty(), newNonTheoryConsts, tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());



		final List<Term> newFormulaConjuncts = new ArrayList<>();
		newFormulaConjuncts.add(tf.getFormula());
//		newFormulaConjuncts.addAll(memlocUpdates);
		newFormulaConjuncts.add(memlocUpdateConjunct);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));
		tfBuilder.setInfeasibility(tf.isInfeasible());
		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);

		return tfBuilder.finishConstruction(mMgdScript);
	}

	private IProgramConst getLocationLiteral(final StoreIndexInfo storeIndexInfo) {
		IProgramConst result = mStoreIndexInfoToLocLiteral.get(storeIndexInfo);
		if (result == null) {
			assert mMgdScript.isLocked();
			final String locLitName = getLocationLitName(storeIndexInfo);
			mMgdScript.declareFun(this, locLitName, new Sort[0], mMemLocSort);
			final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);
			result = new HeapSepProgramConst(locLitTerm);
			mStoreIndexInfoToLocLiteral.put(storeIndexInfo, result);
		}
		return result;
	}

	private String getLocationLitName(final StoreIndexInfo storeIndexInfo) {
		return "mll_" + storeIndexInfo.getEdgeInfo().getSourceLocation() + "_" + mMemLocLitCounter ++;
	}

//	private StoreIndexInfo getOrConstructStoreIndexInfo(final EdgeInfo tfInfo, final Term indexTerm) {
//		StoreIndexInfo sii = mEdgeToIndexToStoreIndexInfo.get(tfInfo, indexTerm);
//		if (sii == null) {
//			sii = new StoreIndexInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
//			mEdgeToIndexToStoreIndexInfo.put(tfInfo, indexTerm, sii);
//		}
//		return sii;
//	}

	public NestedMap2<EdgeInfo, Term, StoreIndexInfo> getEdgeToIndexToStoreIndexInfo() {
		return mEdgeToIndexToStoreIndexInfo;
	}

	/**
	 * Not this class's core concern but it also picks up all ConstantTerms in the program.
	 * @return
	 */
	public Set<ConstantTerm> getAllConstantTerms() {
		if (!TRACK_CONSTANTS) {
			throw new IllegalStateException();
		}
		return mAllConstantTerms;
	}

	public Set<IProgramConst> getLocationLiterals() {
		return new HashSet<>(mStoreIndexInfoToLocLiteral.values());
	}

	public Map<StoreIndexInfo, IProgramConst> getStoreIndexInfoToLocLiteral() {
		return mStoreIndexInfoToLocLiteral;
	}

}



