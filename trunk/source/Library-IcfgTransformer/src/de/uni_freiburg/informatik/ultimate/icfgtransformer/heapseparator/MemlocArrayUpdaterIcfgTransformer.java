package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Applies the "freeze-variables transformation"
 * Performs the following steps:
 *  <li> for each index term that is used in an array update, this introduces a fresh global ProgramVariable, called
 *   the freeze variable, adds a conjunct to the transformula, that nondeterministically assigns the freeze variable the
 *   index term or not.
 *  <li> adds initialization code for all newly introduced freeze variables to the beginning(s) of the program. The
 *   initialization code ensures that initially, a freeze variable is distinct from all other expressions in the program
 *   .. furthermore the valid-array at each freeze variable is set to "1" (this is somewhat hacky, as it is the only
 *   place where the Hoenicke-Lindenmann memory model comes into play..)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class MemlocArrayUpdaterIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

	private final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> mWriteIndexToTfInfoToFreezeVar =
			new NestedMap2<>();

	private final Map<StoreIndexInfo, IProgramConst> mStoreIndexInfoToLocLiteral = new HashMap<>();

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;

	private final static boolean TRACK_CONSTANTS = false;
	private final Set<ConstantTerm> mAllConstantTerms;

	private int mStoreIndexInfoCounter;

	private final IProgramVar mMemlocArrayInt;

	private final Sort mMemLocSort;

	private int mMemLocLitCounter = 0;

	public MemlocArrayUpdaterIcfgTransformer(final ILogger logger,
			final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final IProgramVar memlocArrayInt,
			final Sort memLocSort) {
		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
		mEdgeToIndexToStoreIndexInfo = new NestedMap2<>();
		mAllConstantTerms = TRACK_CONSTANTS ? new HashSet<>() : null;
		mStoreIndexInfoCounter = 0;
		mMemlocArrayInt = memlocArrayInt;
		mMemLocSort = memLocSort;
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		final UnmodifiableTransFormula newTransformula = transformTransformula(oldTransition.getTransformula(),
				new EdgeInfo(oldTransition));
		return super.transform(oldTransition, newSource, newTarget, newTransformula);
	}
//
	public final UnmodifiableTransFormula transformTransformula(final UnmodifiableTransFormula tf,
			final EdgeInfo edgeInfo) {

		if (TRACK_CONSTANTS) {
			/* update the all constants tracking */
			mAllConstantTerms.addAll(new SubTermFinder(t -> t instanceof ConstantTerm)
					.findMatchingSubterms(tf.getFormula())
					.stream().map(t -> (ConstantTerm) t)
					.collect(Collectors.toList()));
		}

		/*
		 * core business from here on..
		 */

		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();

		mMgdScript.lock(this);

		final List<ArrayUpdate> aus = ArrayUpdate.extractArrayUpdates(tf.getFormula(), true);

		final List<Term> memlocUpdates = new ArrayList<>();

		for (final ArrayUpdate au : aus) {

			final IProgramVarOrConst lhsPvoc = edgeInfo.getProgramVarOrConstForTerm(au.getNewArray());
			final IProgramVarOrConst rhsPvoc = edgeInfo.getProgramVarOrConstForTerm(au.getOldArray());
			if (!lhsPvoc.equals(rhsPvoc)){
				/*
				 *  we are only interested in array updates that update one cell here, i.e., the lhs and rhs array must
				 *  refer to the same program variable
				 */
				continue;
			}

			for (int dim = 0; dim < au.getIndex().size(); dim++) {
				final Term indexTerm = au.getIndex().get(dim);

				final StoreIndexInfo storeIndexInfo = getStoreIndexInfo(edgeInfo, indexTerm);
				storeIndexInfo.addArrayAccessDimension(lhsPvoc, dim);

				final IProgramConst locLit = getLocationLiteral(storeIndexInfo);

				final TermVariable memlocIntInVar;
				final TermVariable memlocIntOutVar;

				if (!extraInVars.containsKey(mMemlocArrayInt)) {
					assert !extraOutVars.containsKey(mMemlocArrayInt);
					memlocIntInVar = mMgdScript.constructFreshCopy(mMemlocArrayInt.getTermVariable());
					memlocIntOutVar = mMgdScript.constructFreshCopy(mMemlocArrayInt.getTermVariable());
					extraInVars.put(mMemlocArrayInt, memlocIntInVar);
					extraOutVars.put(mMemlocArrayInt, memlocIntOutVar);
				} else {
					assert extraOutVars.containsKey(mMemlocArrayInt);
					memlocIntInVar = extraInVars.get(mMemlocArrayInt);
					memlocIntOutVar = extraOutVars.get(mMemlocArrayInt);
				}
				assert extraInVars.containsKey(mMemlocArrayInt) && extraOutVars.containsKey(mMemlocArrayInt);


				/* memloc_int[indexTerm] := locLit */
				final Term arrayUpdateTerm = SmtUtils.binaryEquality(mMgdScript.getScript(),
						memlocIntOutVar,
						SmtUtils.store(mMgdScript.getScript(), memlocIntInVar, indexTerm, locLit.getTerm()));

				memlocUpdates.add(arrayUpdateTerm);
			}
		}

		mMgdScript.unlock(this);

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		newInVars.putAll(extraInVars);

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		newOutVars.putAll(extraOutVars);

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars,
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());


		final List<Term> newFormulaConjuncts = new ArrayList<>();
		newFormulaConjuncts.add(tf.getFormula());
		newFormulaConjuncts.addAll(memlocUpdates);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));
		tfBuilder.setInfeasibility(tf.isInfeasible());
		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);

		return tfBuilder.finishConstruction(mMgdScript);
	}

	private IProgramConst getLocationLiteral(final StoreIndexInfo storeIndexInfo) {
		IProgramConst result = mStoreIndexInfoToLocLiteral.get(storeIndexInfo);
		if (result == null) {
			mMgdScript.lock(this);
			final String locLitName = getLocationLitName(storeIndexInfo);
			mMgdScript.declareFun(this, locLitName, new Sort[0], mMemLocSort);
			final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);
			result = new HeapSepProgramConst(locLitTerm);
			mMgdScript.unlock(this);
		}
		return result;
	}

	private String getLocationLitName(final StoreIndexInfo storeIndexInfo) {
		return "mll_" + storeIndexInfo.getEdgeInfo().getSourceLocation() + "_" + mMemLocLitCounter ++;
	}

	private StoreIndexInfo getStoreIndexInfo(final EdgeInfo tfInfo, final Term indexTerm) {
		StoreIndexInfo sii = mEdgeToIndexToStoreIndexInfo.get(tfInfo, indexTerm);
		if (sii == null) {
			sii = new StoreIndexInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
			mEdgeToIndexToStoreIndexInfo.put(tfInfo, indexTerm, sii);
		}
		return sii;
	}

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

