/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * Replace integer division and modulo by auxiliary variables and add 
 * linear constraints that define these auxiliary variables.
 * 
 * We use the semantics of SMTLIB2 where the remainder is always positive.
 * http://smtlib.cs.uiowa.edu/theories/Ints.smt2
 * This is different from the semantics of C99 where "truncation towards 0" is
 * used
 * http://www.open-std.org/JTC1/SC22/WG14/www/docs/n1256.pdf (Section 6.5.5)
 * 
 * Does not check if all statements are linear.
 * 
 * TODO: (Matthias) this transformation is probably not equivalent if
 * divisor is 0. But I think in this will lead to problems before this
 * transformation is used.
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class RewriteDivision extends TransformerPreProcessor {
	private static final String s_DivAuxPrefix = "div_aux";
	private static final String s_ModAuxPrefix = "mod_aux";
	
	/**
	 * Collection of all generated auxiliary variables and the terms
	 * that they replace.
	 * These variables are *not* added to in- or outVars.
	 */
	private final Map<TermVariable, Term> m_auxVars;
	
	/**
	 * Factory for construction of auxVars.
	 */
	private final ReplacementVarFactory m_VarFactory;
	
	/**
	 * Terms for the auxiliary variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> m_auxTerms;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of auxiliary variables. 
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each auxiliary variable
	 * in the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = false;
	
	/**
	 * Constructor
	 */
	public RewriteDivision(ReplacementVarFactory varFactory) {
		super();
		m_VarFactory = varFactory;
		m_auxVars = new LinkedHashMap<TermVariable, Term>();
		m_auxTerms = new ArrayList<Term>();
	}
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	
	@Override
	protected TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		// Clear the data structures
		m_auxVars.clear();
		m_auxTerms.clear();
		
		// Call parent that applies the TermTransformer
		TransFormulaLR new_tf = super.process(script, tf);
		
		// Add auxTerms to the transition
		Term formula = new_tf.getFormula();
		Term auxTerms = Util.and(script, m_auxTerms.toArray(new Term[0]));
		new_tf.setFormula(Util.and(script, formula, auxTerms));
		new_tf.addAuxVars(m_auxVars.keySet());
		
		return new_tf;
	}
	
	@Override
	protected boolean checkSoundness(Script script, TransFormulaLR oldTF,
			TransFormulaLR newTF) {
		Term old_term = oldTF.getFormula();
		Term old_term_with_def = Util.and(script, old_term,
				Util.and(script, m_auxTerms.toArray(new Term[0])));
		Term new_term = newTF.getFormula();
		boolean fail1 = s_CheckResult &&
				isIncorrect(script, old_term_with_def, new_term);
		boolean fail2 = s_CheckResultWithQuantifiers &&
				isIncorrectWithQuantifiers(script, old_term_with_def, new_term);
		return !fail1 || fail2;
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(Script script, Term input, Term result) {
		return LBool.SAT == Util.checkSat(script,
				script.term("distinct", input, result));
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify auxiliary variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Script script, Term input,
			Term result) {
		Term quantified;
		if (m_auxVars.size() > 0) {
			quantified = script.quantifier(Script.EXISTS,
					m_auxVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = script.term("true");
		}
		return Util.checkSat(script,
				script.term("distinct", input, quantified)) == LBool.SAT;
	}
	
	@Override
	protected TermTransformer getTransformer(Script script) {
		return new RewriteDivisionTransformer(script);
	}
	
	/**
	 * Replace integer division and modulo by auxiliary variables and
	 * add definitions of these auxiliary variables.
	 */
	private class RewriteDivisionTransformer extends TermTransformer {
		private final Script m_Script;
		
		RewriteDivisionTransformer(Script script) {
			assert script != null;
			m_Script = script;
		}
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String func = appTerm.getFunction().getName();
			if (func.equals("div")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = m_VarFactory.getOrConstructAuxVar(
						s_DivAuxPrefix + dividend.toString() + divisor.toString(),
						appTerm.getSort());
				m_auxVars.put(quotientAuxVar, appTerm);
				Term divAuxTerm = computeDivAuxTerms(
						dividend, divisor, quotientAuxVar);
				m_auxTerms.add(divAuxTerm);
				setResult(quotientAuxVar);
				return;
			} else if (func.equals("mod")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = m_VarFactory.getOrConstructAuxVar(
						s_DivAuxPrefix + dividend.toString() + divisor.toString(),
						appTerm.getSort());
				m_auxVars.put(quotientAuxVar,
						m_Script.term("div", dividend, divisor));
				TermVariable remainderAuxVar =
						m_VarFactory.getOrConstructAuxVar(
						s_ModAuxPrefix + dividend.toString() + divisor.toString(),
						appTerm.getSort());
				m_auxVars.put(remainderAuxVar, appTerm);
				Term modAuxTerms = computeModAuxTerms(dividend,
						divisor, quotientAuxVar, remainderAuxVar);
				m_auxTerms.add(modAuxTerms);
				setResult(remainderAuxVar);
				return;
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
		}

		/**
 		 * Return the conjunction of the following two formulas
 		 * <pre>
 		 * divisor > 0 ==> quotientAuxVar * divisor <= dividend < (quotientAuxVar+1) * divisor
		 * divisor < 0 ==> quotientAuxVar * divisor <= dividend < (quotientAuxVar-1) * divisor
		 * </pre>
		 * This conjunction is equivalent to the formula
		 * (= quotientAuxVar (div dividend divisor)).
		 * We return the result
		 * <li> in DNF and
		 * <li> in an <i>optimized</i> way where strict inequalities are
		 * replaced by non-strict inequalities.
		 */
		private Term computeDivAuxTerms(Term dividend, Term divisor,
				TermVariable quotientAuxVar) {
			Term[] disjuncts = new Term[2];
			Term one = m_Script.numeral(BigInteger.ONE);
			Term minusOne = m_Script.term("-", one);
			Term divisorIsNegative = m_Script.term("<=", divisor, minusOne);
			Term divisorIsPositive = m_Script.term(">=", divisor, one);
			Term quotientMulDivisor = m_Script.term("*", quotientAuxVar, divisor);
			Term isLowerBound = m_Script.term("<=", quotientMulDivisor, dividend);
			Term strictUpperBoundPosDivisor = m_Script.term(
					"*", m_Script.term("+", quotientAuxVar, one), divisor);
			Term upperBoundPosDivisor = m_Script.term(
					"-", strictUpperBoundPosDivisor, one);
			Term strictUpperBoundNegDivisor = m_Script.term(
					"*", m_Script.term("-", quotientAuxVar, one), divisor);
			Term upperBoundNegDivisor = m_Script.term(
					"-", strictUpperBoundNegDivisor, one);
			Term isUpperBoundPosDivisor = m_Script.term(
					"<=", dividend, upperBoundPosDivisor);
			Term isUpperBoundNegDivisor = m_Script.term(
					"<=", dividend, upperBoundNegDivisor);
			disjuncts[0] = Util.and(m_Script, 
					divisorIsPositive, isLowerBound, isUpperBoundPosDivisor);
			disjuncts[1] = Util.and(m_Script, 
					divisorIsNegative, isLowerBound, isUpperBoundNegDivisor);
			return Util.or(m_Script, disjuncts);
		}
		
		/**
		 * Return the conjunction of the following three formulas
		 * <pre>
 		 * dividend = quotientAuxVar * divisor + remainderAuxVar
		 * divisor > 0 ==> 0 <= remainderAuxVar < divisor
		 * divisor < 0 ==> 0 <= remainderAuxVar < -divisor
		 * </pre>
		 * This conjunction is equivalent to the conjunction of the following 
		 * two formulas. 
		 * (= quotientAuxVar (div dividend divisor))
		 * (= remainderAuxVar (mod dividend divisor))
 		 * We return the result
		 * <li> in DNF and
		 * <li> in an <i>optimized</i> way where strict inequalities are
		 * replaced by non-strict inequalities.
		 */
		private Term computeModAuxTerms(Term dividend, Term divisor,
				TermVariable quotientAuxVar, TermVariable remainderAuxVar) {
			Term[] disjuncts = new Term[2];
			Term one = m_Script.numeral(BigInteger.ONE);
			Term minusOne = m_Script.term("-", one);
			Term divisorIsNegative = m_Script.term("<=", divisor, minusOne);
			Term divisorIsPositive = m_Script.term(">=", divisor, one);
			Term zero = m_Script.numeral(BigInteger.ZERO);
			Term isLowerBound = m_Script.term("<=", zero, remainderAuxVar);
			Term upperBoundPosDivisor = m_Script.term("-", divisor, one);
			Term isUpperBoundPosDivisor = 
					m_Script.term("<=", remainderAuxVar, upperBoundPosDivisor);
			Term upperBoundNegDivisor = 
					m_Script.term("-", m_Script.term("-", divisor), one);
			Term isUpperBoundNegDivisor = 
					m_Script.term("<=", remainderAuxVar, upperBoundNegDivisor);
			Term equality = m_Script.term("=", dividend, 
					m_Script.term("+", m_Script.term("*", 
							quotientAuxVar, divisor), remainderAuxVar));
			disjuncts[0] = Util.and(m_Script, divisorIsPositive, isLowerBound, 
					isUpperBoundPosDivisor, equality);
			disjuncts[1] = Util.and(m_Script, divisorIsNegative, isLowerBound, 
					isUpperBoundNegDivisor, equality);
			return Util.or(m_Script, disjuncts);
		}
	}
}