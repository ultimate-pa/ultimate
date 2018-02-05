package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.math.BigInteger;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
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

	private final Set<IProgramConst> mFreezeLiterals;

	private final Map<IProgramNonOldVar, IProgramConst> mFreezeVarTofreezeVarLit;
	private final IProgramVar mValidArray;

	public FreezeVarInitializer(final ILogger logger, //final CfgSmtToolkit csToolkit,
			final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit, final IProgramVar validArray) {
		super(logger, //csToolkit,
				resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);
//		computeInitializingTerm(freezeVarTofreezeVarLit, validArray);
		mFreezeVarTofreezeVarLit = freezeVarTofreezeVarLit;
		mValidArray = validArray;

		mFreezeLiterals = new HashSet<>(freezeVarTofreezeVarLit.values());
	}



	@Override
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
//		assert mInitializingTerm != null && mFreezeVarInVars != null && mFreezeVarOutVars != null && mFreezeLiterals != null;


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


			final ComputeInitializingTerm cit =
				new ComputeInitializingTerm(mFreezeVarTofreezeVarLit, mValidArray, oldTransformula);


			final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(oldTransformula.getInVars());
			newInVars.putAll(cit.getFreezeVarInVars());

			final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(oldTransformula.getOutVars());
			newOutVars.putAll(cit.getFreezeVarOutVars());

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
			/*
			 * conjoin the original transformula with the initializing term
			 */
			final Term newFormula = SmtUtils.and(script, oldTransformula.getFormula(), cit.getInitializingTerm());

			newTfBuilder.setFormula(newFormula);
			newTfBuilder.setInfeasibility(oldTransformula.isInfeasible());
			newTfBuilder.addAuxVarsButRenameToFreshCopies(oldTransformula.getAuxVars(), mMgdScript);

			final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);

			return super.transform(oldTransition, newSource, newTarget, newTransformula);
		} else {
			// not an initial transition, do nothing
			return super.transform(oldTransition, newSource, newTarget);
		}
	}

	class ComputeInitializingTerm {

		// result fields
		private Term mInitializingTerm;
		private Map<IProgramVar, TermVariable> mFreezeVarInVars;
		private Map<IProgramVar, TermVariable> mFreezeVarOutVars;

//		private UnmodifiableTransFormula mOriginalTransFormula;

		ComputeInitializingTerm(final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit,
				final IProgramVar validArray, final UnmodifiableTransFormula originalTransFormula) {
//			mOriginalTransFormula = originalTransFormula;
			computeInitializingTerm(freezeVarTofreezeVarLit, validArray, originalTransFormula);
		}

		private void computeInitializingTerm(final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit,
				final IProgramVar validArray, final UnmodifiableTransFormula originalTransFormula) {
			mFreezeVarInVars = new HashMap<>();
			mFreezeVarOutVars = new HashMap<>();


			TermVariable validArrayTv = originalTransFormula.getOutVars().get(validArray);
			if (validArrayTv == null) {
				// originalTransFormula does not constrain valid
				assert originalTransFormula.getInVars().get(validArray) == null : "#valid is havocced in an initial "
						+ "transformula -- somewhat unexpected.. --> TODO: treat this case";
				validArrayTv = mMgdScript.constructFreshTermVariable(validArray.getGloballyUniqueId(),
						validArray.getSort());
				mFreezeVarInVars.put(validArray, validArrayTv);
				mFreezeVarOutVars.put(validArray, validArrayTv);
			}

			// is this locking necessary? the script is used for creating Terms only
			mMgdScript.lock(this);

			final List<Term> initializingEquations = new ArrayList<>();
			for (final Entry<IProgramNonOldVar, IProgramConst> en : freezeVarTofreezeVarLit.entrySet()) {
				// "frz_l_x"
//				final TermVariable frzVarTv = en.getKey().getTermVariable();
				final TermVariable frzVarTv = mMgdScript.constructFreshTermVariable(en.getKey().getGloballyUniqueId(),
						en.getKey().getSort());
				// "lit_frz_l_x"
				final Term frzLit = en.getValue().getTerm();

				// "frz_l_x = lit_frz_l_x"
				initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), frzVarTv, frzLit));
				mFreezeVarInVars.put(en.getKey(), frzVarTv);
				mFreezeVarOutVars.put(en.getKey(), frzVarTv);

				/*
				 *  "valid[lit_frz_l_x] = 1"
				 */
				// TODO have to get the valid Termvariable from the Transformula or make a new one!
				final Term select = SmtUtils.select(mMgdScript.getScript(), validArrayTv, frzLit);
				final Term one = SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE);

				initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), select, one));
			}


			/*
			 * furthermore add disequalities between all freeze var literals
			 */
			final List<Term> freezeLitDisequalities = new ArrayList<>();
			if (HeapSepSettings.ASSUME_FREEZE_VAR_LIT_DISEQUALITIES_AT_INIT_EDGES) {
				for (final Entry<IProgramConst, IProgramConst> en : CrossProducts.binarySelectiveCrossProduct(
						new HashSet<>(freezeVarTofreezeVarLit.values()), false, false)) {
					freezeLitDisequalities.add(
							mMgdScript.getScript().term("not",
									mMgdScript.term(this, "=", en.getKey().getTerm(), en.getValue().getTerm())));
				}
			}

			mInitializingTerm = SmtUtils.and(mMgdScript.getScript(),
					SmtUtils.and(mMgdScript.getScript(), initializingEquations),
					SmtUtils.and(mMgdScript.getScript(), freezeLitDisequalities));

			mMgdScript.unlock(this);

		}

		public Term getInitializingTerm() {
			return mInitializingTerm;
		}

		public Map<IProgramVar, TermVariable> getFreezeVarInVars() {
			return mFreezeVarInVars;
		}

		public Map<IProgramVar, TermVariable> getFreezeVarOutVars() {
			return mFreezeVarOutVars;
		}
	}
}
