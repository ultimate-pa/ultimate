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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarFactory;


/**
 * Replace integer division and modulo by replacement variables and add 
 * linear constraints that define these replacement variables.
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
public class RewriteDivision implements PreProcessor {
	private static final String s_DivRepPrefix = "div_rep";
	private static final String s_ModRepPrefix = "mod_rep";
	
	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;
	
	/**
	 * Collection of all generated replacement variables and the terms
	 * that they replace.
	 * These variables are *not* added to in- or outVars.
	 */
	private final Map<TermVariable, Term> m_repVars;
	
	/**
	 * The replacement terms for the replacement variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> m_repTerms;
	
	/**
	 * For generating replacement variables
	 */
	private final VarCollector m_rankVarCollector;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of replacement variables. 
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each replacement variable
	 * in the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = false;
	
	public RewriteDivision(VarCollector rankVarCollector) {
		m_rankVarCollector = rankVarCollector;
		m_repVars = new LinkedHashMap<TermVariable, Term>();
		m_repTerms = new ArrayList<Term>();
	}
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	
	@SuppressWarnings("unused")
	@Override
	public Term process(Script script, Term term) {
		assert m_Script == null;
		m_Script = script;
		Term result = (new RewriteDivisionHelper()).transform(term);
		if (m_repTerms.size() > 0) {
			Term repTerms = Util.and(m_Script, m_repTerms.toArray(new Term[0]));
			result = Util.and(script, result, repTerms);
			
			assert !s_CheckResult || !isIncorrect(term, result, repTerms) 
					: "rewrite division unsound";
			assert !s_CheckResultWithQuantifiers
					||	!isIncorrectWithQuantifiers(term, result, repTerms) 
					: "rewrite division unsound";
		}
		
		return result;
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the replacement
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result, Term repTerm) {
		Term inputWithDefinitions = m_Script.term("and", input, repTerm);
		return LBool.SAT == Util.checkSat(m_Script,
				m_Script.term("distinct",  inputWithDefinitions, result));
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify replacement variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result,
			Term repTerm) {
		Term quantified;
		if (m_repVars.size() > 0) {
			quantified = m_Script.quantifier(Script.EXISTS,
					m_repVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		return Util.checkSat(m_Script, m_Script.term("distinct", 
				input, quantified)) == LBool.SAT;
	}
	
	/**
	 * Replace integer division and modulo by replacement variables and
	 * add definitions of these replacement variables.
	 */
	private class RewriteDivisionHelper extends TermTransformer {
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			VarFactory rvFactory = m_rankVarCollector.getFactory();
			String func = appTerm.getFunction().getName();
			if (func.equals("div")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientRepVar = rvFactory.getNewTermVariable(
						s_DivRepPrefix, appTerm.getSort());
				m_repVars.put(quotientRepVar, appTerm);
				Term divRepTerm = computeDivReplacementTerms(
						dividend, divisor, quotientRepVar);
				m_repTerms.add(divRepTerm);
				setResult(quotientRepVar);
				return;
			} else if (func.equals("mod")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientRepVar = rvFactory.getNewTermVariable(
						s_DivRepPrefix,
						appTerm.getSort()
				);
				m_repVars.put(quotientRepVar,
						m_Script.term("div", dividend, divisor));
				TermVariable remainderRepVar = rvFactory.getNewTermVariable(
						s_ModRepPrefix, appTerm.getSort());
				m_repVars.put(remainderRepVar, appTerm);
				Term modRepTerms = computeModReplacementTerms(dividend,
						divisor, quotientRepVar, remainderRepVar);
				m_repTerms.add(modRepTerms);
				setResult(remainderRepVar);
				return;
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
		}

		/**
 		 * Return the conjunction of the following two formulas
 		 * <pre>
 		 * divisor > 0 ==> quotientRepVar * divisor <= dividend < (quotientRepVar+1) * divisor
		 * divisor < 0 ==> quotientRepVar * divisor <= dividend < (quotientRepVar-1) * divisor
		 * </pre>
		 * This conjunction is equivalent to the formula
		 * (= quotientRepVar (div dividend divisor)).
		 * We return the result
		 * <li> in DNF and
		 * <li> in an <i>optimized</i> way where strict inequalities are
		 * replaced by non-strict inequalities.
		 */
		private Term computeDivReplacementTerms(Term dividend, Term divisor,
				TermVariable quotientRepVar) {
			Term[] disjuncts = new Term[2];
			Term one = m_Script.numeral(BigInteger.ONE);
			Term minusOne = m_Script.term("-", one);
			Term divisorIsNegative = m_Script.term("<=", divisor, minusOne);
			Term divisorIsPositive = m_Script.term(">=", divisor, one);
			Term quotientMulDivisor = m_Script.term("*", quotientRepVar, divisor);
			Term isLowerBound = m_Script.term("<=", quotientMulDivisor, dividend);
			Term strictUpperBoundPosDivisor = m_Script.term(
					"*", m_Script.term("+", quotientRepVar, one), divisor);
			Term upperBoundPosDivisor = m_Script.term(
					"-", strictUpperBoundPosDivisor, one);
			Term strictUpperBoundNegDivisor = m_Script.term(
					"*", m_Script.term("-", quotientRepVar, one), divisor);
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
 		 * dividend = quotientRepVar * divisor + remainderRepVar
		 * divisor > 0 ==> 0 <= remainderRepVar < divisor
		 * divisor < 0 ==> 0 <= remainderRepVar < -divisor
		 * </pre>
		 * This conjunction is equivalent to the conjunction of the following 
		 * two formulas. 
		 * (= quotientRepVar (div dividend divisor))
		 * (= remainderRepVar (mod dividend divisor))
 		 * We return the result
		 * <li> in DNF and
		 * <li> in an <i>optimized</i> way where strict inequalities are
		 * replaced by non-strict inequalities.
		 */
		private Term computeModReplacementTerms(Term dividend, Term divisor,
				TermVariable quotientRepVar, TermVariable remainderRepVar) {
			Term[] disjuncts = new Term[2];
			Term one = m_Script.numeral(BigInteger.ONE);
			Term minusOne = m_Script.term("-", one);
			Term divisorIsNegative = m_Script.term("<=", divisor, minusOne);
			Term divisorIsPositive = m_Script.term(">=", divisor, one);
			Term zero = m_Script.numeral(BigInteger.ZERO);
			Term isLowerBound = m_Script.term("<=", zero, remainderRepVar);
			Term upperBoundPosDivisor = m_Script.term("-", divisor, one);
			Term isUpperBoundPosDivisor = 
					m_Script.term("<=", remainderRepVar, upperBoundPosDivisor);
			Term upperBoundNegDivisor = 
					m_Script.term("-", m_Script.term("-", divisor), one);
			Term isUpperBoundNegDivisor = 
					m_Script.term("<=", remainderRepVar, upperBoundNegDivisor);
			Term equality = m_Script.term("=", dividend, 
					m_Script.term("+", m_Script.term("*", 
							quotientRepVar, divisor), remainderRepVar));
			disjuncts[0] = Util.and(m_Script, divisorIsPositive, isLowerBound, 
					isUpperBoundPosDivisor, equality);
			disjuncts[1] = Util.and(m_Script, divisorIsNegative, isLowerBound, 
					isUpperBoundNegDivisor, equality);
			return Util.or(m_Script, disjuncts);
		}
	}
}