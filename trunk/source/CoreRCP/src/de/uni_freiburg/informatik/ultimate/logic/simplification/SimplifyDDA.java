package de.uni_freiburg.informatik.ultimate.logic.simplification;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Simplify formulas, but keep their Boolean structure.
 * Replace subformulas by true or false if this replacement leads to an
 * equivalent formula.
 * Based on the paper "Small Formulas for Large Programms: On-Line Constraint
 * Simplification in Scalable Static Analysis" by Isil Dillig, Thomas Dillig
 * and Alex Aiken.
 * This implementation extends this approach to formulas which are not in NNF,
 * contain "=>" and "ite".
 * 
 * @author heizmann@informatik.uni-freiburg.de, Jochen Hoenicke, Markus Pomrehn
 *
 */
public class SimplifyDDA {
	private final Script m_Script;
	private final Logger m_Logger;
	private final Term m_True;
	private final Term m_False;
	
	/**
	 * The constructor gets the script interface and the logger for output
	 */
	public SimplifyDDA(final Script script, final Logger logger) 
			throws SMTLIBException {
		m_Script = script;
		m_Logger = logger;
		m_True = m_Script.term("true");
		m_False = m_Script.term("false");
	}
	
	/**
	 * Redundancy is a property of a subterm B with respect to its term A.
	 * The subterm B is called:
	 * <ul>
	 * <li> NON_RELAXING if term A is equivalent to the term, where B is replaced
	 * by false.
	 * <li> NON_CONSTRAINING if term A is equivalent to the term, where B is
	 * replaced by true.
	 * <li> NOT_REDUNDANT B is neither NON_REAXING nor NON_CONSTRAINING with
	 * respect to A.
	 * </ul>
	 */
	public enum Redundancy {
		NON_RELAXING, NON_CONSTRAINING, NOT_REDUNDANT
	}
	
	/**
	 * Checks if termA is equivalent to termB.
	 * Returns unsat if the terms are equivalent, sat if they are not and
	 * unknown if it is not possible to determine.
	 */
	public LBool checkEquivalence (Term termA, Term termB) throws SMTLIBException {
		Term equivalentTestTerm = m_Script.term("=", termA, termB);
		LBool areTermsEquivalent = 
				Util.checkSat(m_Script, Util.not(m_Script, equivalentTestTerm));
		return areTermsEquivalent;
		
	}
	
	/**
	 * Checks if term is redundant, with respect to the critical constraint
	 * on the assertion stack.
	 * @return NON_CONSTRAINING if term is equivalent to true,
	 * NON_RELAXING if term is equivalent to true,
	 * NOT_REDUNDANT if term is not redundant.
	 */
	private Redundancy getRedundancy (Term term)
			throws SMTLIBException {
		LBool isTermConstraining =
				Util.checkSat(m_Script, Util.not(m_Script, term));
		if (isTermConstraining == LBool.UNSAT) {
			return Redundancy.NON_CONSTRAINING;
		}
				
		LBool isTermRelaxing = Util.checkSat(m_Script, term);
		if (isTermRelaxing == LBool.UNSAT) {
			return Redundancy.NON_RELAXING;
		}
		
		return Redundancy.NOT_REDUNDANT;
	}
	
	private static Term termVariable2constant(Script script, TermVariable tv) 
			throws SMTLIBException {
		String name = tv.getName() + "_const_" + tv.hashCode();
		Sort[] paramSorts = {};
		Sort resultSort = tv.getSort();
		script.declareFun(name, paramSorts, resultSort);
		Term result = script.term(name);
		return result;
	}

	/**
	 * Return a Term which is equivalent to term but whose number of leaves is
	 * less than or equal to the number of leaves in term.
	 * @return term if each subterm of term is neither NON_CONSTRAINING
	 * nor NON_RELAXING. Otherwise return a copy of term, where each
	 * NON_CONSTRAINING subterm is replaced by true and each NON_RELAXING
	 * subterm is replaced by false
	 * @param term whose Sort is Boolean
	 */
	public Term getSimplifiedTerm(Term inputTerm) throws SMTLIBException {
//		m_Logger.debug("Simplifying " + term);
		Term term =inputTerm;
		m_Script.push(1);
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i=0; i<vars.length; i++) {
			values[i] = termVariable2constant(m_Script, vars[i]);
		}
		term = m_Script.let(vars, values, term);

		term = new FormulaUnLet().unlet(term);
		term = this.simplifySubTerm(term);
		
		term = new TermTransformer() {
			@Override
			public void convert(Term term) {
				for (int i = 0; i < vars.length; i++)
					if (term == values[i])
						term = vars[i];
				super.convert(term);
			}
		}.transform(term);
		m_Script.pop(1);
		m_Logger.debug(new DebugMessage("Simplified to: {0}", term));
		assert (checkEquivalence(inputTerm, term) != LBool.SAT) : "Simplification Unsound";
		return term;
	}
	
	
	/**
	 * Simplify the inputTerm with respect to the critical constraint on the
	 * assertion stack of m_Script.
	 * 
	 * We use the algorithm by Dillig, Dillig, Aiken.  The function is
	 * recursively called.
	 * <ul>
	 * <li> We simplify a sibling of an "and" under the assumption that all other
	 * siblings hold.
	 * <li> We simplify a sibling of an "or" under the assumption that all other
	 * siblings do not hold.
	 * <li> We simplify a sibling of "=>" under the corresponding assumptions.
	 * <li> We simplify ite as follows: The condition without further 
	 * assumptions, the if part under the assumption that the condition holds,
	 * the else part under the assumption that the condition does not hold.
	 * </ul> 
	 * 
	 * @param inputTerm term whose Sort is Boolean
	 */
	private Term simplifySubTerm(Term inputTerm)	throws SMTLIBException {
		if (inputTerm instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) inputTerm;
			Term[] parameters = applicationTerm.getParameters();
			Term[] newParameters = new Term[parameters.length];
			
			final String connective = applicationTerm.getFunction().getName();
			
			if (connective == "not") {
				return Util.not(m_Script, this.simplifySubTerm(parameters[0]));
			}
				
			if (connective == "ite") {
				Term simpCond = this.simplifySubTerm(parameters[0]);
				m_Script.push(1);
				m_Script.assertTerm(simpCond);
				Term simpThen = this.simplifySubTerm(parameters[1]);
				m_Script.pop(1);
				m_Script.push(1);
				m_Script.assertTerm(Util.not(m_Script, simpCond));
				Term simpElse = this.simplifySubTerm(parameters[2]);
				m_Script.pop(1);
				return Util.ite(m_Script, simpCond, simpThen, simpElse);
			}
			if (connective == "and" || connective == "or" || connective == "=>") {
				boolean parameterSimplifiedInLastIteration = true;
				boolean parameterSimplifiedInAnyIteration = false;
				while (parameterSimplifiedInLastIteration) {
					
					parameterSimplifiedInLastIteration = false;
					// create n pushes with the original constraints on it.
					m_Script.push(1);
					for (int i = parameters.length-1; i > 0; i--) {
						m_Script.push(1);
						final Term contribution = negateSibling(
								parameters[i], connective, i, parameters.length);
						m_Script.assertTerm(contribution);
					}

					for (int i = 0; i < parameters.length; i++) {
						// push all already simplified siblings
						for (int k=0; k < i; k++) {
							final Term contribution = negateSibling(
									newParameters[k], connective, k, parameters.length);
							m_Script.assertTerm(contribution);
						}
						// simplify parameter recursively
						newParameters[i] = this.simplifySubTerm(parameters[i]);
						m_Script.pop(1);
						final Term earlyResult;
						if (newParameters[i] == m_False) {
							if (connective == "and") {
								earlyResult = m_False;
							} else if (connective == "=>" && i != parameters.length-1) {
								earlyResult = m_True;
							} else {
								earlyResult = null;
							}
						} else if (newParameters[i] == m_True) {
							if (connective == "or") {
								earlyResult = m_True;
							} else if (connective == "=>" && i == parameters.length-1) {
								earlyResult = m_True;
							} else {
								earlyResult = null;
							}
						} else {
							earlyResult = null;
						}
						
						if (earlyResult != null) {
							while (++i < parameters.length) {
								m_Script.pop(1);
							}
							return earlyResult;
						} 
						
						if (newParameters[i] != parameters[i]) {
							parameterSimplifiedInLastIteration = true;
							parameterSimplifiedInAnyIteration = true;
						}
					}
					parameters = newParameters;
				}
				// if a parameter was simplified
				if (parameterSimplifiedInAnyIteration) {
					// Building the return term
					if (connective == "and") {
						return Util.and(m_Script, newParameters);
					} else if (connective == "or") {
						return Util.or(m_Script, newParameters);
					} else if (connective == "=>") {
						return Util.implies(m_Script, newParameters);
					} else {
						throw new AssertionError("unknown connective");
					}
				}
				// no parameter could be simplified so return the input term
				else {
					return inputTerm;
				}
				
			}
		}
		Redundancy redundancy = this.getRedundancy(inputTerm);
		switch (redundancy) {
				case NON_CONSTRAINING: return m_True;
				case NON_RELAXING: return m_False;
				default: return inputTerm;
		}
	}
	
	/**
	 * Returns the contribution of a sibling to the critical constraint. This is
	 * either the sibling itself or its negation. The result is the negated
	 * sibling iff
	 * <ul>
	 * <li> the connective is "or"
	 * <li> the connective is "=>" and i==n-1
	 * </ul>
	 * 
	 * @param i Index of this sibling. E.g., sibling B has index 1 in the term
	 * (and A B C)
	 * @param n Number of all siblings. E.g., the term (and A B C) has three
	 * siblings.
	 */
	private Term negateSibling(Term sibling, String connective, int i, int n) {
		final boolean negate = (connective == "or" || connective == "=>" && i == n-1);
		if (negate) {
			return Util.not(m_Script, sibling);
		} else {
			return sibling;
		}
	}
	
	
}
