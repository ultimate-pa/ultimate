package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxVarGenerator;


/**
 * Replace integer division and modulo by auxiliary variables and add 
 * (auxiliary)linear constraints that define these auxiliary variables.
 * 
 * Does not check if all statements are linear.
 * 
 * TOOD: (Matthias) this transformation is probably not equivalent if
 * divisor is 0. But I think in this will lead to problems before this
 * transformation is used.
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class RewriteDivision implements PreProcessor {
	private static final String s_DivAuxPrefix = "div_aux";
	private static final String s_ModAuxPrefix = "mod_aux";
	
	private Script m_Script;
	private AuxVarGenerator m_AuxVarGenerator;
	private Collection<Term> m_AuxTerms;
	
	/**
	 * Maps each new auxiliary variable to an equivalent term without 
	 * these new auxiliary variables.
	 */
	private Map<TermVariable,Term> m_AuxVar2Definition = 
			new HashMap<TermVariable,Term>();
	
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
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	
	@Override
	public Term process(Script script, Term term) {
		assert m_Script == null;
		assert m_AuxVarGenerator == null;
		assert m_AuxTerms == null;
		m_Script = script;
		m_AuxVarGenerator = new AuxVarGenerator(script, term);
		m_AuxTerms = new ArrayList<Term>();
		Term result = (new RewriteDivisionHelper()).transform(term);
		result = Util.and(script, result,
				Util.and(script, m_AuxTerms.toArray(new Term[0])));
		
		assert !s_CheckResult || !isIncorrect(term, result);
		assert !s_CheckResultWithQuantifiers || !isIncorrectWithQuantifiers(term, result);
		
		return result;
	}
	
	/**
	 * @return the auxiliary variables generated during the process
	 */
	public Collection<TermVariable> getAuxVars() {
		return m_AuxVarGenerator.getAuxVars();
	}
	
	private Term conjunctionOfAuxVarDefintions() {
		Term[] conjunction = new Term[m_AuxVar2Definition.size()];
		int i=0;
		for (Entry<TermVariable, Term> entry  : m_AuxVar2Definition.entrySet()) {
			conjunction[i] = m_Script.term("=", entry.getKey(), entry.getValue());
			i++;
		}
		return Util.and(m_Script, conjunction);
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result) {
		Term inputWithDefinitions = 
				m_Script.term("and", input, conjunctionOfAuxVarDefintions()); 
		return (Util.checkSat(m_Script, m_Script.term("distinct", 
				inputWithDefinitions, result)) != LBool.SAT);
	}

	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify auxiliary variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result) {
		Term quantified;
		if (m_AuxVarGenerator.getAuxVars().size() > 0) {
			quantified = m_Script.quantifier(0, 
					m_AuxVarGenerator.getAuxVars().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		assert (Util.checkSat(m_Script, m_Script.term("distinct", 
				input, quantified)) != LBool.SAT);
		
		
		Term inputWithDefinitions = 
				m_Script.term("and", input, conjunctionOfAuxVarDefintions()); 
		return (Util.checkSat(m_Script, m_Script.term("distinct", 
				inputWithDefinitions, result)) != LBool.SAT);
	}
	
	
	
	/**
	 * Replace integer division and modulo by auxiliary variables and
	 * add definitions of these auxiliary variables to  m_AuxTerms.
	 *
	 */
	private class RewriteDivisionHelper extends TermTransformer {
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String func = appTerm.getFunction().getName();
			if (func.equals("div")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = m_AuxVarGenerator.newAuxVar(
						s_DivAuxPrefix,	m_Script.sort("Int"));
				addDivAuxVarDefinition(dividend, divisor, quotientAuxVar);
				Term divAuxiliaryTerm = computeDivAuxiliaryTerms(
						dividend, divisor, quotientAuxVar);
				m_AuxTerms.add(divAuxiliaryTerm);
				setResult(quotientAuxVar);
				return;
			} else if (func.equals("mod")) {
				assert(appTerm.getParameters().length == 2);
				Term dividend = newArgs[0];
				Term divisor = newArgs[1];
				TermVariable quotientAuxVar = m_AuxVarGenerator.newAuxVar(
						s_DivAuxPrefix,	m_Script.sort("Int"));
				TermVariable remainderAuxVar = m_AuxVarGenerator.newAuxVar(
						s_ModAuxPrefix,	m_Script.sort("Int"));
				addModAuxVarDefinition(dividend, divisor, quotientAuxVar, 
						remainderAuxVar);
				Term modAuxiliaryTerms = computeModAuxiliaryTerms(dividend, 
						divisor, quotientAuxVar, remainderAuxVar);
				m_AuxTerms.add(modAuxiliaryTerms);
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
		 * <li> an <i>optimized</i> variation where strict inequalities are
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
		 * Store the auxiliary variable definition
		 * quotientAuxVar = divident / divisor
		 */
		private void addDivAuxVarDefinition(Term dividend, Term divisor,
				TermVariable quotientAuxVar) {
			m_AuxVar2Definition.put(quotientAuxVar, 
					m_Script.term("div", dividend, divisor));
		}

		/**
		 * Store the auxiliary variable definitions
		 * quotientAuxVar = divident / divisor
		 * remainderAuxVar = divident % divisor
		 */
		private void addModAuxVarDefinition(Term dividend, Term divisor,
				TermVariable quotientAuxVar, TermVariable remainderAuxVar) {
			m_AuxVar2Definition.put(quotientAuxVar, 
					m_Script.term("div", dividend, divisor));
			m_AuxVar2Definition.put(remainderAuxVar, 
					m_Script.term("mod", dividend, divisor));
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
		 * <li> an <i>optimized</i> variation where strict inequalities are
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