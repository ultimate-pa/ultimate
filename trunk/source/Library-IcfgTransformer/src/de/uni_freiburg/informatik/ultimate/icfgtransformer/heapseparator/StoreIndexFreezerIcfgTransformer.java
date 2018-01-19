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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
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

	private final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> mWriteIndexToTfInfoToFreezeVar =
			new NestedMap2<>();

	private final Map<StoreIndexInfo, IProgramNonOldVar> mArrayAccessInfoToFreezeVar = new HashMap<>();

//	private final DefaultIcfgSymbolTable mNewSymbolTable;

	public StoreIndexFreezerIcfgTransformer(final ILogger logger,
//			final CfgSmtToolkit csToolkit,
			final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker) {
		super(logger, //csToolkit,
				resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
//		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		final UnmodifiableTransFormula newTransformula = transformTransformula(oldTransition.getTransformula(),
				new EdgeInfo(oldTransition));
		return super.transform(oldTransition, newSource, newTarget, newTransformula);

//		if (oldTransition instanceof IcfgInternalTransition) {
//			// TODO: is this the right payload?
//			return mEdgeFactory.createInternalTransition(newSource, newTarget, oldTransition.getPayload(),
//					newTransformula);
//		} else if (oldTransition instanceof IcfgCallTransition) {
//			final IcfgCallTransition newCallTransition = mEdgeFactory.createCallTransition(newSource, newTarget,
//					oldTransition.getPayload(), newTransformula);
//			mOldCallToNewCall.put((IcfgCallTransition) oldTransition, newCallTransition);
//			return newCallTransition;
//		} else if (oldTransition instanceof IcfgReturnTransition) {
//			final IcfgCallTransition correspondingNewCall =
//					mOldCallToNewCall.get(((IcfgReturnTransition) oldTransition).getCorrespondingCall());
//			assert correspondingNewCall != null;
//			return mEdgeFactory.createReturnTransition(newSource, newTarget, correspondingNewCall,
//					oldTransition.getPayload(), newTransformula, correspondingNewCall.getLocalVarsAssignment());
//		} else {
//			throw new IllegalArgumentException("unknown transition type");
//		}
	}
//
	public final UnmodifiableTransFormula transformTransformula(final UnmodifiableTransFormula tf,
			final EdgeInfo tfInfo) {
		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();

		final List<Term> indexUpdateFormula = new ArrayList<>();

		mMgdScript.lock(this);

		final List<ArrayUpdate> aus = new ArrayUpdateExtractor(false, false, tf.getFormula()).getArrayUpdates();

		// collect all terms that are used as an index in an array update
		final Set<Term> indexTerms = new HashSet<>();
		for (final ArrayUpdate au : aus) {
			indexTerms.addAll(au.getIndex());
		}

		final List<Term> indexUpdates = new ArrayList<>();

		for (final Term indexTerm : indexTerms) {
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

		return tfBuilder.finishConstruction(mMgdScript);
	}

	private IProgramNonOldVar getFreezeVariable(final Term indexTerm, final EdgeInfo tfInfo) {
//		IProgramNonOldVar result = mWriteIndexToTfInfoToFreezeVar.get(indexTerm, tfInfo);

		final StoreIndexInfo aai = new StoreIndexInfo(tfInfo, indexTerm);
		IProgramNonOldVar result = mArrayAccessInfoToFreezeVar.get(aai);

		if (result == null) {
			result = ProgramVarUtils.constructGlobalProgramVarPair(
						indexTerm.toString().replace("|", "") + "_frz", indexTerm.getSort(),
						mMgdScript, this);
			/*
			 *  we don't need to do anything for the symbol table here it seems, because the TransformedIcfgBuilder
			 *  recognizes new variables in the TransFormula
			 */
//			mNewSymbolTable.add(result);
//			mWriteIndexToTfInfoToFreezeVar.put(indexTerm, tfInfo, result);
			mArrayAccessInfoToFreezeVar.put(aai, result);
		}
		return result;
	}

//	public NestedMap2<Term, EdgeInfo, IProgramNonOldVar> getWriteIndexToTfInfoToFreezeVar() {
//		return mWriteIndexToTfInfoToFreezeVar;
//	}

	public Map<StoreIndexInfo, IProgramNonOldVar> getArrayAccessInfoToFreezeVar() {
		return mArrayAccessInfoToFreezeVar;
	}

}

