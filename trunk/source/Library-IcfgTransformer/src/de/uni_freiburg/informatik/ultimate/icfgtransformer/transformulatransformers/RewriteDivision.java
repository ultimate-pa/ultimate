/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Replace integer division and modulo by auxiliary variables and add linear constraints that define these auxiliary
 * variables.
 * 
 * We use the semantics of SMTLIB2 where the remainder is always positive. http://smtlib.cs.uiowa.edu/theories/Ints.smt2
 * This is different from the semantics of C99 where "truncation towards 0" is used
 * http://www.open-std.org/JTC1/SC22/WG14/www/docs/n1256.pdf (Section 6.5.5)
 * 
 * Does not check if all statements are linear.
 * 
 * TODO: (Matthias) this transformation is probably not equivalent if divisor is 0. But I think in this will lead to
 * problems before this transformation is used.
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class RewriteDivision extends TransformerPreprocessor {
	public static final String DESCRIPTION = "Replace integer division by equivalent linear constraints";

	private static final String DIV_AUX_PREFIX = "div_aux";
	private static final String MOD_AUX_PREFIX = "mod_aux";

	/**
	 * Use assert statement to check if result is equivalent to the conjunction of input term and definition of
	 * auxiliary variables.
	 */
	private static final boolean CHECK_RESULT = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula that is obtained by existentially
	 * quantifying each auxiliary variable in the result term.
	 */
	private static final boolean CHECK_RESULT_WITH_QUAMTIFIERS = false;

	/**
	 * Collection of all generated auxiliary variables and the terms that they replace. These variables are *not* added
	 * to in- or outVars.
	 */
	private final Map<TermVariable, Term> mAuxVars;

	/**
	 * Factory for construction of auxVars.
	 */
	private final ReplacementVarFactory mVarFactory;

	/**
	 * Terms for the auxiliary variables for the formula. These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> mAuxTerms;

	/**
	 * Constructor
	 */
	public RewriteDivision(final ReplacementVarFactory varFactory) {
		super();
		mVarFactory = varFactory;
		mAuxVars = new LinkedHashMap<>();
		mAuxTerms = new ArrayList<>();
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf) throws TermException {
		// Clear the data structures
		mAuxVars.clear();
		mAuxTerms.clear();

		// Call parent that applies the TermTransformer
		final ModifiableTransFormula new_tf = super.process(script, tf);

		// Add auxTerms to the transition
		final Term formula = new_tf.getFormula();
		final Term auxTerms = SmtUtils.and(script.getScript(), mAuxTerms.toArray(new Term[mAuxTerms.size()]));
		new_tf.setFormula(SmtUtils.and(script.getScript(), formula, auxTerms));
		new_tf.addAuxVars(mAuxVars.keySet());

		return new_tf;
	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		final Term old_term = oldTF.getFormula();
		final Term old_termwith_def =
				SmtUtils.and(script, old_term, SmtUtils.and(script, mAuxTerms.toArray(new Term[mAuxTerms.size()])));
		final Term new_term = newTF.getFormula();
		final boolean fail1 = CHECK_RESULT && isIncorrect(script, old_termwith_def, new_term);
		final boolean fail2 =
				CHECK_RESULT_WITH_QUAMTIFIERS && isIncorrectWithQuantifiers(script, old_termwith_def, new_term);
		return !fail1 && !fail2;
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For this check we add to the input term the
	 * definition of the auxiliary variables.
	 */
	private boolean isIncorrect(final Script script, final Term input, final Term result) {
		return LBool.SAT == Util.checkSat(script, script.term("distinct", input, result));
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For this check we existentially quantify
	 * auxiliary variables in the result term.
	 */
	private boolean isIncorrectWithQuantifiers(final Script script, final Term input, final Term result) {
		Term quantified;
		if (!mAuxVars.isEmpty()) {
			quantified = script.quantifier(Script.EXISTS, mAuxVars.keySet().toArray(new TermVariable[mAuxVars.size()]),
					result);
		} else {
			quantified = script.term("true");
		}
		return Util.checkSat(script, script.term("distinct", input, quantified)) == LBool.SAT;
	}

	@Override
	protected TermTransformer getTransformer(final ManagedScript script) {
		return new RewriteDivisionTransformer(script.getScript());
	}

	/**
	 * Replace integer division and modulo by auxiliary variables and add definitions of these auxiliary variables.
	 */
	private class RewriteDivisionTransformer extends TermTransformer {
		private final Script mScript;

		RewriteDivisionTransformer(final Script script) {
			assert script != null;
			mScript = script;
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String func = appTerm.getFunction().getName();
			if (func.equals("div")) {
				assert appTerm.getParameters().length == 2;
				final Term dividend = newArgs[0];
				final Term divisor = newArgs[1];
				final TermVariable quotientAuxVar = mVarFactory.getOrConstructAuxVar(
						DIV_AUX_PREFIX + dividend.toString() + divisor.toString(), appTerm.getSort());
				mAuxVars.put(quotientAuxVar, appTerm);
				final Term divAuxTerm = computeDivAuxTerms(dividend, divisor, quotientAuxVar);
				mAuxTerms.add(divAuxTerm);
				setResult(quotientAuxVar);
				return;
			} else if (func.equals("mod")) {
				assert appTerm.getParameters().length == 2;
				final Term dividend = newArgs[0];
				final Term divisor = newArgs[1];
				final TermVariable quotientAuxVar = mVarFactory.getOrConstructAuxVar(
						DIV_AUX_PREFIX + dividend.toString() + divisor.toString(), appTerm.getSort());
				mAuxVars.put(quotientAuxVar, mScript.term("div", dividend, divisor));
				final TermVariable remainderAuxVar = mVarFactory.getOrConstructAuxVar(
						MOD_AUX_PREFIX + dividend.toString() + divisor.toString(), appTerm.getSort());
				mAuxVars.put(remainderAuxVar, appTerm);
				final Term modAuxTerms = computeModAuxTerms(dividend, divisor, quotientAuxVar, remainderAuxVar);
				mAuxTerms.add(modAuxTerms);
				setResult(remainderAuxVar);
				return;
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
		}

		/**
		 * Return the conjunction of the following two formulas
		 * 
		 * <pre>
		 * divisor > 0 ==> quotientAuxVar * divisor <= dividend < (quotientAuxVar+1) * divisor
		 * divisor < 0 ==> quotientAuxVar * divisor <= dividend < (quotientAuxVar-1) * divisor
		 * </pre>
		 * 
		 * This conjunction is equivalent to the formula (= quotientAuxVar (div dividend divisor)). We return the result
		 * <li>in DNF and
		 * <li>in an <i>optimized</i> way where strict inequalities are replaced by non-strict inequalities.
		 */
		private Term computeDivAuxTerms(final Term dividend, final Term divisor, final TermVariable quotientAuxVar) {
			final Term[] disjuncts = new Term[2];
			final Term one = SmtUtils.constructIntValue(mScript, BigInteger.ONE);
			final Term minusOne = mScript.term("-", one);
			final Term divisorIsNegative = mScript.term("<=", divisor, minusOne);
			final Term divisorIsPositive = mScript.term(">=", divisor, one);
			final Term quotientMulDivisor = mScript.term("*", quotientAuxVar, divisor);
			final Term isLowerBound = mScript.term("<=", quotientMulDivisor, dividend);
			final Term strictUpperBoundPosDivisor = mScript.term("*", mScript.term("+", quotientAuxVar, one), divisor);
			final Term upperBoundPosDivisor = mScript.term("-", strictUpperBoundPosDivisor, one);
			final Term strictUpperBoundNegDivisor = mScript.term("*", mScript.term("-", quotientAuxVar, one), divisor);
			final Term upperBoundNegDivisor = mScript.term("-", strictUpperBoundNegDivisor, one);
			final Term isUpperBoundPosDivisor = mScript.term("<=", dividend, upperBoundPosDivisor);
			final Term isUpperBoundNegDivisor = mScript.term("<=", dividend, upperBoundNegDivisor);
			disjuncts[0] = SmtUtils.and(mScript, divisorIsPositive, isLowerBound, isUpperBoundPosDivisor);
			disjuncts[1] = SmtUtils.and(mScript, divisorIsNegative, isLowerBound, isUpperBoundNegDivisor);
			return SmtUtils.or(mScript, disjuncts);
		}

		/**
		 * Return the conjunction of the following three formulas
		 * 
		 * <pre>
		 * dividend = quotientAuxVar * divisor + remainderAuxVar
		 * divisor > 0 ==> 0 <= remainderAuxVar < divisor
		 * divisor < 0 ==> 0 <= remainderAuxVar < -divisor
		 * </pre>
		 * 
		 * This conjunction is equivalent to the conjunction of the following two formulas. (= quotientAuxVar (div
		 * dividend divisor)) (= remainderAuxVar (mod dividend divisor)) We return the result
		 * <li>in DNF and
		 * <li>in an <i>optimized</i> way where strict inequalities are replaced by non-strict inequalities.
		 */
		private Term computeModAuxTerms(final Term dividend, final Term divisor, final TermVariable quotientAuxVar,
				final TermVariable remainderAuxVar) {
			final Term[] disjuncts = new Term[2];
			final Term one = SmtUtils.constructIntValue(mScript, BigInteger.ONE);
			final Term minusOne = mScript.term("-", one);
			final Term divisorIsNegative = mScript.term("<=", divisor, minusOne);
			final Term divisorIsPositive = mScript.term(">=", divisor, one);
			final Term zero = SmtUtils.constructIntValue(mScript, BigInteger.ZERO);
			final Term isLowerBound = mScript.term("<=", zero, remainderAuxVar);
			final Term upperBoundPosDivisor = mScript.term("-", divisor, one);
			final Term isUpperBoundPosDivisor = mScript.term("<=", remainderAuxVar, upperBoundPosDivisor);
			final Term upperBoundNegDivisor = mScript.term("-", mScript.term("-", divisor), one);
			final Term isUpperBoundNegDivisor = mScript.term("<=", remainderAuxVar, upperBoundNegDivisor);
			final Term equality = mScript.term("=", dividend,
					mScript.term("+", mScript.term("*", quotientAuxVar, divisor), remainderAuxVar));
			disjuncts[0] = SmtUtils.and(mScript, divisorIsPositive, isLowerBound, isUpperBoundPosDivisor, equality);
			disjuncts[1] = SmtUtils.and(mScript, divisorIsNegative, isLowerBound, isUpperBoundNegDivisor, equality);
			return SmtUtils.or(mScript, disjuncts);
		}
	}
}
