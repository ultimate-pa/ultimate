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
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
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
public class StoreIndexFreezerIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

//	private final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> mWriteIndexToTfInfoToFreezeVar =
//			new NestedMap2<>();

	private final Map<StoreIndexInfo, IProgramNonOldVar> mStoreIndexInfoToFreezeVar = new HashMap<>();

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;

	private final Set<ConstantTerm> mAllConstantTerms;

	public StoreIndexFreezerIcfgTransformer(final ILogger logger,
			final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final List<IProgramVarOrConst> heapArrays,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo) {
		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
		mAllConstantTerms = new HashSet<>();
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		final UnmodifiableTransFormula newTransformula = transformTransformula(oldTransition.getTransformula(),
				new EdgeInfo(oldTransition));
		return super.transform(oldTransition, newSource, newTarget, newTransformula);
	}

	public final UnmodifiableTransFormula transformTransformula(final UnmodifiableTransFormula tf,
			final EdgeInfo edgeInfo) {

		/*
		 * update the all constants tracking
		 */
		mAllConstantTerms.addAll(new SubTermFinder(t -> t instanceof ConstantTerm)
				.findMatchingSubterms(tf.getFormula()).stream().map(t -> (ConstantTerm) t)
				.collect(Collectors.toList()));

		/*
		 * core business from here on..
		 */

		if (mEdgeToIndexToStoreIndexInfo.get(edgeInfo) == null) {
			// edge does not have any array writes --> return it unchanged
			return tf;
		}

		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();

		mMgdScript.lock(this);



		final List<Term> freezeVarUpdates = new ArrayList<>();
		for (final Entry<Term, StoreIndexInfo> en : mEdgeToIndexToStoreIndexInfo.get(edgeInfo).entrySet()) {
			final StoreIndexInfo storeIndexInfo = en.getValue();

			final Term indexTerm = storeIndexInfo.getIndexTerm();

			final IProgramNonOldVar freezeVar = getOrConstructFreezeVariable(storeIndexInfo);

			final TermVariable inputFreezeIndexTv;
			final TermVariable updatedFreezeIndexTv;
			if (!extraInVars.containsKey(freezeVar)) {
				assert !extraOutVars.containsKey(freezeVar);
				inputFreezeIndexTv = mMgdScript.constructFreshCopy(freezeVar.getTermVariable());
				updatedFreezeIndexTv = mMgdScript.constructFreshCopy(freezeVar.getTermVariable());
				extraInVars.put(freezeVar, inputFreezeIndexTv);
				extraOutVars.put(freezeVar, updatedFreezeIndexTv);
			} else {
				assert extraOutVars.containsKey(freezeVar);
				inputFreezeIndexTv = extraInVars.get(freezeVar);
				updatedFreezeIndexTv = extraOutVars.get(freezeVar);
			}
			assert extraInVars.containsKey(freezeVar) && extraOutVars.containsKey(freezeVar);

			/*
			 * construct the nondeterministic update "freezeIndex' = freezeIndex \/ freezeIndex' = storeIndex"
			 */
			freezeVarUpdates.add(SmtUtils.or(mMgdScript.getScript(),
					mMgdScript.term(this, "=", updatedFreezeIndexTv, indexTerm),
					mMgdScript.term(this, "=", updatedFreezeIndexTv, inputFreezeIndexTv)));
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
//		newFormulaConjuncts.addAll(indexUpdateFormula);
		newFormulaConjuncts.addAll(freezeVarUpdates);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));

		tfBuilder.setInfeasibility(tf.isInfeasible());

//		tf.getAuxVars().forEach(tfBuilder::addAuxVar);
		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);


		return tfBuilder.finishConstruction(mMgdScript);
	}

	private IProgramNonOldVar getOrConstructFreezeVariable(final StoreIndexInfo storeIndexInfo) {
		final Term indexTerm = storeIndexInfo.getIndexTerm();

		IProgramNonOldVar result = mStoreIndexInfoToFreezeVar.get(storeIndexInfo);

		if (result == null) {
			result = ProgramVarUtils.constructGlobalProgramVarPair(
						indexTerm.toString().replace("|", "").replace("v_", "") + "_" + storeIndexInfo.getId() + "_frz",
						indexTerm.getSort(), mMgdScript, this);
			/*
			 *  we don't need to do anything for the symbol table here it seems, because the TransformedIcfgBuilder
			 *  recognizes new variables in the TransFormula
			 */
//			mNewSymbolTable.add(result);
//			mWriteIndexToTfInfoToFreezeVar.put(indexTerm, tfInfo, result);
			mStoreIndexInfoToFreezeVar.put(storeIndexInfo, result);
		}
		return result;
	}

//	private StoreIndexInfo getStoreIndexInfo(final EdgeInfo tfInfo, final Term indexTerm) {
//		StoreIndexInfo sii = mEdgeToIndexToStoreIndexInfo.get(tfInfo, indexTerm);
//		if (sii == null) {
//			sii = new StoreIndexInfo(tfInfo, indexTerm, mStoreIndexInfoCounter++);
//			mEdgeToIndexToStoreIndexInfo.put(tfInfo, indexTerm, sii);
//		}
//		return sii;
//	}

//	public NestedMap2<Term, EdgeInfo, IProgramNonOldVar> getWriteIndexToTfInfoToFreezeVar() {
//		return mWriteIndexToTfInfoToFreezeVar;
//	}

	public Map<StoreIndexInfo, IProgramNonOldVar> getArrayAccessInfoToFreezeVar() {
		return mStoreIndexInfoToFreezeVar;
	}

	public NestedMap2<EdgeInfo, Term, StoreIndexInfo> getEdgeToIndexToStoreIndexInfo() {
		return mEdgeToIndexToStoreIndexInfo;
	}

	/**
	 * Not this class's core concern but it also picks up all ConstantTerms in the program.
	 * @return
	 */
	public Set<ConstantTerm> getAllConstantTerms() {
		return mAllConstantTerms;
	}

}

