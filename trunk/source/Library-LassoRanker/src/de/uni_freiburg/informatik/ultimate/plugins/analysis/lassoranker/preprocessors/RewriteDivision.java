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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVarFactory;


/**
 * Replace integer division and modulo by auxiliary variables and add 
 * (auxiliary) linear constraints that define these auxiliary variables.
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
	private static final String s_DivAuxPrefix = "div_aux";
	private static final String s_ModAuxPrefix = "mod_aux";
	
	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;
	
	/**
	 * Collection of all generated auxiliary variables and the terms
	 * that they replace.
	 * These variables are *not* added to in- or outVars.
	 */
	private Map<TermVariable, Term> m_auxVars;
	
	/**
	 * The auxiliary terms defining the auxiliary variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private Collection<Term> m_auxTerms;
	
	/**
	 * For generating auxiliary variables
	 */
	private final RankVarCollector m_rankVarCollector;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of auxiliary variables. 
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each auxiliary variable in
	 * the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = true;
	
	public RewriteDivision(RankVarCollector rankVarCollector) {
		m_rankVarCollector = rankVarCollector;
		m_auxVars = new HashMap<TermVariable, Term>();
		m_auxTerms = new ArrayList<Term>();
	}
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	
	@Override
	public Term process(Script script, Term term) {
		assert m_Script == null;
		m_Script = script;
		Term result = (new RewriteDivisionHelper()).transform(term);
		if (m_auxTerms.size() > 0) {
			Term auxTerm = Util.and(m_Script, m_auxTerms.toArray(new Term[0]));
			result = Util.and(script, result, auxTerm);
			
/*			assert !s_CheckResult || !isIncorrect(term, result) 
					: "rewrite division unsound";
			assert !s_CheckResultWithQuantifiers
					||	!isIncorrectWithQuantifiers(term, result) 
					: "rewrite division unsound"; */
		}
		
		return result;
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result) {
		Term[] defs = m_auxVars.values().toArray(new Term[0]);
		Term inputWithDefinitions = 
				m_Script.term("and", input, Util.and(m_Script, defs));
		return LBool.SAT == Util.checkSat(m_Script,
				m_Script.term("distinct",  inputWithDefinitions, result));
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify auxiliary variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result) {
		Term quantified;
		if (m_auxVars.size() > 0) {
			quantified = m_Script.quantifier(Script.EXISTS,
					m_auxVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		assert Util.checkSat(m_Script, m_Script.term("distinct", 
				input, quantified)) != LBool.SAT;
		
		Term auxTerm = Util.and(m_Script, m_auxTerms.toArray(new Term[0]));
		Term inputWithDefinitions = m_Script.term("and", input, auxTerm); 
		return LBool.SAT == Util.checkSat(m_Script,
				m_Script.term("distinct",  inputWithDefinitions, result));
	}
	
	/**
	 * Replace integer division and modulo by auxiliary variables and
	 * add definitions of these auxiliary variables.
	 */
	private class RewriteDivisionHelper extends TermTransformer {
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			RankVarFactory rvFactory = m_rankVarCollector.getFactory();
			String func = appTerm.getFunction().getName();
			if (func.equals("div")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = rvFactory.getNewTermVariable(
						s_DivAuxPrefix, appTerm.getSort());
				m_auxVars.put(quotientAuxVar, appTerm);
				Term divAuxiliaryTerm = computeDivAuxiliaryTerms(
						dividend, divisor, quotientAuxVar);
				m_auxTerms.add(divAuxiliaryTerm);
				setResult(quotientAuxVar);
				return;
			} else if (func.equals("mod")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = rvFactory.getNewTermVariable(
						s_DivAuxPrefix,
						appTerm.getSort()
				);
				m_auxVars.put(quotientAuxVar,
						m_Script.term("div", dividend, divisor));
				TermVariable remainderAuxVar = rvFactory.getNewTermVariable(
						s_ModAuxPrefix, appTerm.getSort());
				m_auxVars.put(remainderAuxVar, appTerm);
				Term modAuxiliaryTerms = computeModAuxiliaryTerms(dividend,
						divisor, quotientAuxVar, remainderAuxVar);
				m_auxTerms.add(modAuxiliaryTerms);
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
		private Term computeDivAuxiliaryTerms(Term dividend, Term divisor,
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
		private Term computeModAuxiliaryTerms(Term dividend, Term divisor,
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