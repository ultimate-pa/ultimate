package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

class FreezeVarInitializingTransformulaBuilder {

	// result fields
	private Term mInitializingTerm;
	private Map<IProgramVar, TermVariable> mFreezeVarInVars;
	private Map<IProgramVar, TermVariable> mFreezeVarOutVars;

	private final HeapSepSettings mSettings;
	private UnmodifiableTransFormula mInitializingTransformula;

	private final ManagedScript mMgdScript;

	FreezeVarInitializingTransformulaBuilder(final ManagedScript mgdScript,
			final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit,
			final IProgramVar validArray, //final UnmodifiableTransFormula originalTransFormula,
			final HeapSepSettings settings) {
		mMgdScript = Objects.requireNonNull(mgdScript);
		mSettings = Objects.requireNonNull(settings);
		computeInitializingTerm(Objects.requireNonNull(freezeVarTofreezeVarLit),
				Objects.requireNonNull(validArray));//,
				//Objects.requireNonNull(originalTransFormula));
		computeInitializingTransformula(new HashSet<>(freezeVarTofreezeVarLit.values()));
	}

	public UnmodifiableTransFormula getInitializingTransformula() {
		return mInitializingTransformula;
	}

	private void computeInitializingTerm(final Map<IProgramNonOldVar, IProgramConst> freezeVarTofreezeVarLit,
			final IProgramVar validArray) {
		mFreezeVarInVars = new HashMap<>();
		mFreezeVarOutVars = new HashMap<>();

		TermVariable validArrayTv = null;
		if (validArrayTv == null) {
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
		if (mSettings.isAssumeFreezeVarLitDisequalitiesAtInitEdges()) {
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

	private Term getInitializingTerm() {
		return mInitializingTerm;
	}

	private Map<IProgramVar, TermVariable> getFreezeVarInVars() {
		return mFreezeVarInVars;
	}

	private Map<IProgramVar, TermVariable> getFreezeVarOutVars() {
		return mFreezeVarOutVars;
	}

	private UnmodifiableTransFormula computeInitializingTransformula(final Set<IProgramConst> freezeLiterals) {
		/*
		 *  <li> add a conjunct with equalities l_x_frz = lit_l_x_frz (l means a location) to the Transformula's
		 *    formula
		 *  <li> add all l_x_frz as assigned vars to the invars/outvars
		 */
		final Map<IProgramVar, TermVariable> newInVars = getFreezeVarInVars();

		final Map<IProgramVar, TermVariable> newOutVars = getFreezeVarOutVars();

		/*
		 * Note that the symbol table will be automatically updated with the new constants by the
		 *  TransformedIcfgBuilder (in its .finish() method).
		 */
		final Set<IProgramConst> newNonTheoryConstants = freezeLiterals;

		final TransFormulaBuilder newTfBuilder = new TransFormulaBuilder(
				newInVars, newOutVars, newNonTheoryConstants.isEmpty(), newNonTheoryConstants,
				true, null, true);

		final Term newFormula = getInitializingTerm();

		newTfBuilder.setFormula(newFormula);
		newTfBuilder.setInfeasibility(Infeasibility.UNPROVEABLE);

		final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);
		return newTransformula;
	}
}