package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class StoreIndexFreezerIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

//	private final Map<ArrayIndex, List<IProgramNonOldVar>> mStoreIndexToFreezeIndex = new HashMap<>();


	private final NestedMap2<Term, TfInfo, IProgramNonOldVar> mWriteIndexToTfInfoToFreezeVar =
			new NestedMap2<>();
	private final DefaultIcfgSymbolTable mNewSymbolTable;

	public StoreIndexFreezerIcfgTransformer(final ILogger logger, final CfgSmtToolkit csToolkit, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker) {
		super(logger, csToolkit, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {

		if (oldTransition instanceof IcfgInternalTransition) {
			final UnmodifiableTransFormula newTransformula = transform(oldTransition.getTransformula(),
				new TfInfo(oldTransition));

			// TODO: is this the right payload?
			return mEdgeFactory.createInternalTransition(newSource, newTarget, oldTransition.getPayload(),
					newTransformula);
		} else if (oldTransition instanceof IcfgCallTransition) {
			throw new AssertionError("TODO");
		} else if (oldTransition instanceof IcfgReturnTransition) {
			throw new AssertionError("TODO");
		} else {
			throw new IllegalArgumentException("unknown transition type");
		}
	}
//
	public final UnmodifiableTransFormula transform(final UnmodifiableTransFormula tf, final TfInfo tfInfo) {
		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();

		final List<Term> indexUpdateFormula = new ArrayList<>();

		mMgdScript.lock(this);

//		final Set<ArrayIndex> storeIndices = MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula()).stream()
//			.map(mds -> mds.getIndex()).collect(Collectors.toSet());
		final List<ArrayUpdate> aus = new ArrayUpdateExtractor(false, false, tf.getFormula()).getArrayUpdates();


		// collect all terms that are used as an index in an array update
		final Set<Term> indexTerms = new HashSet<>();
		for (final ArrayUpdate au : aus) {
			indexTerms.addAll(au.getIndex());
		}


		final List<Term> indexUpdates = new ArrayList<>();

		for (final Term indexTerm : indexTerms) {
		//			final List<IProgramNonOldVar> freezeIndex = getFreezeVariables(storeIndex, tfInfo);
			final IProgramNonOldVar freezeVar = getFreezeVariable(indexTerm, tfInfo);

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
			indexUpdates.add(SmtUtils.or(mMgdScript.getScript(),
					mMgdScript.term(this, "=", updatedFreezeIndexTv, indexTerm)));
		}



//		for (final ArrayIndex storeIndex : storeIndices) {
//		for (final ArrayUpdate au : aus) {
//			final ArrayIndex storeIndex = au.getIndex();
//
//			final List<Term> indexUpdates = new ArrayList<>();
//		for (final Term indexTerm : indexTerms) {
//
////			final List<IProgramNonOldVar> freezeIndex = getFreezeVariables(storeIndex, tfInfo);
//			final IProgramNonOldVar freezeVar = getFreezeVariable(indexTerm, tfInfo);
//
//			for (int i = 0; i < freezeIndex.size(); i++) {
//				final TermVariable inputFreezeIndexTv;
//				final TermVariable updatedFreezeIndexTv;
//				if (!extraInVars.containsKey(freezeIndex.get(i))) {
//					assert !extraOutVars.containsKey(freezeIndex.get(i));
//					inputFreezeIndexTv = mMgdScript.constructFreshCopy(freezeIndex.get(i).getTermVariable());
//					updatedFreezeIndexTv = mMgdScript.constructFreshCopy(freezeIndex.get(i).getTermVariable());
//					extraInVars.put(freezeIndex.get(i), inputFreezeIndexTv);
//					extraOutVars.put(freezeIndex.get(i), updatedFreezeIndexTv);
//				} else {
//					assert extraOutVars.containsKey(freezeIndex.get(i));
//					inputFreezeIndexTv = extraInVars.get(freezeIndex.get(i));
//					updatedFreezeIndexTv = extraOutVars.get(freezeIndex.get(i));
//				}
//				assert extraInVars.containsKey(freezeIndex.get(i)) && extraOutVars.containsKey(freezeIndex.get(i));
//
//				/*
//				 * construct the nondeterministic update "freezeIndex' = freezeIndex \/ freezeIndex' = storeIndex"
//				 */
//				indexUpdates.add(SmtUtils.or(mMgdScript.getScript(),
//								mMgdScript.term(this, "=", updatedFreezeIndexTv, storeIndex.get(i))));
//			}
//			indexUpdateFormula.add(SmtUtils.and(mMgdScript.getScript(), indexUpdates));
//		}
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
		newFormulaConjuncts.addAll(indexUpdateFormula);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));

		tfBuilder.setInfeasibility(tf.isInfeasible());

		final UnmodifiableTransFormula newTf = tfBuilder.finishConstruction(mMgdScript);

		return tfBuilder.finishConstruction(mMgdScript);
	}

	private IProgramNonOldVar getFreezeVariable(final Term indexTerm, final TfInfo tfInfo) {
		IProgramNonOldVar result = mWriteIndexToTfInfoToFreezeVar.get(indexTerm, tfInfo);
		if (result == null) {
			result = ProgramVarUtils.constructGlobalProgramVarPair(
						indexTerm.toString().replace("|", "") + "_frz", indexTerm.getSort(),
						mMgdScript, this);
			mNewSymbolTable.add(result);
			mWriteIndexToTfInfoToFreezeVar.put(indexTerm, tfInfo, result);
		}
		return result;
	}

//	private final List<IProgramNonOldVar> getFreezeVariables(final ArrayIndex storeIndex, final TfInfo tfInfo) {
//		List<IProgramNonOldVar> result = mStoreIndexToFreezeIndex.get(storeIndex);
//		if (result == null) {
//			result = new ArrayList<>();
//			for (final Term indEl : storeIndex) {
//
//				final IProgramNonOldVar alreadyCreatedPv = mIndexTermToFrozenVar.get(indEl);
//
//				final IProgramNonOldVar freezePv;
//				if (alreadyCreatedPv == null) {
//					freezePv = ProgramVarUtils.constructGlobalProgramVarPair(
//						indEl.toString().replace("|", "") + "_frz", indEl.getSort(),
//						mMgdScript, this);
//					mIndexTermToFrozenVar.put(indEl, freezePv);
//				} else {
//					freezePv = alreadyCreatedPv;
//				}
//				result.add(freezePv);
//				mNewSymbolTable.add(freezePv);
//			}
//			mStoreIndexToFreezeIndex.put(storeIndex, result);
//		}
//		return result;
//	}

}

class TfInfo {
	IcfgEdge mEdge;

	TfInfo(final IcfgEdge edge) {
		mEdge = edge;
	}

}

