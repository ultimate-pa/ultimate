package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class FreezeVarInitializer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

	private Term mInitializingTerm;
	private Set<IProgramConst> mFreezeLiterals;
	private Map<IProgramVar, TermVariable> mFreezeVarInVars;
	private Map<IProgramVar, TermVariable> mFreezeVarOutVars;

	public FreezeVarInitializer(final ILogger logger, //final CfgSmtToolkit csToolkit,
			final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit, final IProgramVar validArray) {
		super(logger, //csToolkit,
				resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
		computeInitializingTerm(freezeVarTofreezeVarLit, validArray);
	}

	private void computeInitializingTerm(final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit,
			final IProgramVar validArray) {
		mFreezeVarInVars = new HashMap<>();
		mFreezeVarOutVars = new HashMap<>();

		// is this locking necessary? the script is used for creating Terms only
		mMgdScript.lock(this);

		final List<Term> initializingEquations = new ArrayList<>();
		for (final Entry<IProgramNonOldVar, IProgramConst> en : freezeVarTofreezeVarLit.entrySet()) {
			// "frz_l_x"
			final TermVariable frzVar = en.getKey().getTermVariable();
			// "lit_frz_l_x"
			final Term frzLit = en.getValue().getTerm();

			// "frz_l_x = lit_frz_l_x"
			initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), frzVar,
					frzLit));
			mFreezeVarOutVars.put(en.getKey(), frzVar);

			// "valid[lit_frz_l_x] = 1"
			final Term select = SmtUtils.select(mMgdScript.getScript(), validArray.getTermVariable(), frzLit);
			final Term one = mMgdScript.getScript().term("1");
			initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), select, one));
		}

		if (!freezeVarTofreezeVarLit.isEmpty()) {
			mFreezeVarInVars.put(validArray, validArray.getTermVariable());
			mFreezeVarOutVars.put(validArray, validArray.getTermVariable());
		}

		mInitializingTerm = SmtUtils.and(mMgdScript.getScript(), initializingEquations);

		mMgdScript.unlock(this);

		mFreezeLiterals = new HashSet<>(freezeVarTofreezeVarLit.values());
	}

	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		assert mInitializingTerm != null && mFreezeVarInVars != null && mFreezeVarOutVars != null && mFreezeLiterals != null;

		final Script script = mMgdScript.getScript();

		if (mInputIcfg.getInitialNodes().contains(oldTransition.getSource())) {
			/*
			 * we have an initial edge --> add the initialization code to the transition
			 *  steps:
			 *  <li> add a conjunct with equalities l_x_frz = lit_l_x_frz (l means a location) to the Transformula's
			 *    formula
			 *  <li> add all l_x_frz as assigned vars to the invars/outvars
			 */
			final UnmodifiableTransFormula oldTransformula = oldTransition.getTransformula();

			final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(oldTransformula.getInVars());
			newInVars.putAll(mFreezeVarInVars);
			final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(oldTransformula.getOutVars());
			newOutVars.putAll(mFreezeVarOutVars);

			/*
			 * Note that the symbol table will be automatically updated with the new constants by the
			 *  TransformedIcfgBuilder (in its .finish() method).
			 */
			final Set<IProgramConst> newNonTheoryConstants = DataStructureUtils.union(
					oldTransformula.getNonTheoryConsts(), mFreezeLiterals);

			final TransFormulaBuilder newTfBuilder = new TransFormulaBuilder(
					newInVars, newOutVars, newNonTheoryConstants.isEmpty(), newNonTheoryConstants,
					oldTransformula.getBranchEncoders().isEmpty(), oldTransformula.getBranchEncoders(),
					oldTransformula.getAuxVars().isEmpty());

			// TODO: do we need to lock the mgdscript here??
			final Term newFormula = SmtUtils.and(script, oldTransformula.getFormula(), mInitializingTerm);

			newTfBuilder.setFormula(newFormula);
			newTfBuilder.setInfeasibility(oldTransformula.isInfeasible());

			final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);

			return super.transform(oldTransition, newSource, newTarget, newTransformula);
		} else {
			// not an initial transition, do nothing
			return super.transform(oldTransition, newSource, newTarget);
		}
	}

}
