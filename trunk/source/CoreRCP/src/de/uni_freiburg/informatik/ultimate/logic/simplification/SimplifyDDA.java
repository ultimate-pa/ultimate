package de.uni_freiburg.informatik.ultimate.logic.simplification;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Class to simplify Application terms with connective "and" or "or", other
 * terms are considered as literals and stay unchanged.
 * Based on the paper "Small Formulas for Large Programms: On-Line Constraint
 * Simplification in Scalable Static Analysis"
 * By Isil Dillig, Thomas Dillig and Alex Aiken
 * @author Markus Pomrehn
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
//			m_Logger.debug(nonConstrainingTestTerm + " is valid");
			return Redundancy.NON_CONSTRAINING;
		}
				
		LBool isTermRelaxing = Util.checkSat(m_Script, term);
		if (isTermRelaxing == LBool.UNSAT) {
//			m_Logger.debug(nonRelaxingTestTerm + " is valid");
			return Redundancy.NON_RELAXING;
		}
		
		return Redundancy.NOT_REDUNDANT;
	}
	
	private Term addNegation(Term t, boolean isNegated) {
		if (isNegated)
			return Util.not(m_Script, t);
		else
			return t;
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
		term = this.getSimplifiedTerm(term, false);
		
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
		m_Logger.debug("Simplified to: " + term);
		assert (checkEquivalence(inputTerm, term) == LBool.UNSAT);
		return term;
	}
	

	/**
	 * Simplify the inputTerm, or (not inputTerm) if isNegated is set.
	 * The script may contain some assumptions and the inputTerm should
	 * be simplified under these assumptions.
	 * 
	 * We use the algorithm by Dillig, Dillig, Aiken.  The function is
	 * recursively called.  For a conjunction we assume that all sibling
	 * formulas hold (otherwise the conjunction is false anyway) and for
	 * a disjunction we assume that all siblings are false.  
	 * 
	 * We also support ite, where the then part is simplified under the
	 * assumption that the condition is true, and the else part is 
	 * simplified under the assumption that the condition is false.
	 * 
	 * @param inputTerm term whose Sort is Boolean
	 * @param isNegated true if negated inputTerm should be simplified.
	 */
	private Term getSimplifiedTerm(Term inputTerm, boolean isNegated)
			throws SMTLIBException {
		if (inputTerm instanceof ApplicationTerm) {
			// Cast
			ApplicationTerm applicationTerm = (ApplicationTerm) inputTerm;
			// C
			Term[] parameters = applicationTerm.getParameters();
			// C'
			HashSet<Term> newParameters = new HashSet<Term>();
			
			String connective = applicationTerm.getFunction().getName();
			Boolean parameterSimplified = true;
			
			if (connective == "not")
				return this.getSimplifiedTerm(parameters[0], !isNegated);
			if (connective == "ite") {
				Term cond = this.getSimplifiedTerm(parameters[0], false);
				m_Script.push(1);
				m_Script.assertTerm(cond);
				Term simpThen = this.getSimplifiedTerm(parameters[1], isNegated);
				m_Script.pop(1);
				m_Script.push(1);
				m_Script.assertTerm(Util.not(m_Script, cond));
				Term simpElse = this.getSimplifiedTerm(parameters[2], isNegated);
				m_Script.pop(1);
				if (cond == m_True || simpThen == simpElse) 
					return simpThen;
				else if (cond == m_False) 
					return simpElse;
				else if (simpThen == m_True) 
					return Util.or(m_Script, cond, simpElse);
				else if (simpElse == m_False) 
					return Util.and(m_Script, cond, simpThen);
				else if (simpThen == m_False) 
					return Util.and(m_Script, Util.not(m_Script, cond), simpElse);
				else if (simpElse == m_True) 
					return Util.or(m_Script, Util.not(m_Script, cond), simpThen);
				return m_Script.term("ite", cond, simpThen, simpElse);
			}
			if (connective == "and" || connective == "or" || connective == "=>") {
				boolean isAnd = (connective == "and") != isNegated; 
				while (parameterSimplified) {
					parameterSimplified = false;
					// create n pushes with the original constraints on it.
					m_Script.push(1);
					for (int i = parameters.length-1; i > 0; i--) {
						boolean paramNegated = isNegated != (connective == "=>" && i < parameters.length - 1); 
						m_Script.push(1);
						m_Script.assertTerm(addNegation(parameters[i], isAnd == paramNegated));
					}
					for (int i = 0; i < parameters.length; i++) {
						boolean paramNegated = isNegated != (connective == "=>" && i < parameters.length - 1); 
						// push other already simplified parameters
						for (Term sibling : newParameters) {
							m_Script.assertTerm(addNegation(sibling, !isAnd));
						}
						// simplify parameter recursively
						Term simplifiedParameter = this.getSimplifiedTerm(
								parameters[i], paramNegated);
						m_Script.pop(1);
						if (simplifiedParameter == m_True) {
							if (isAnd) {
								parameterSimplified = true;
							} else {
								while (++i < parameters.length) {
									m_Script.pop(1);
								}
								return m_True;
							}
						} else if (simplifiedParameter == m_False) {
							if (isAnd) {
								while (++i < parameters.length) {
									m_Script.pop(1);
								}
								return m_False;
							}
							else { 
								parameterSimplified = true;
							}
						} else {
							if (simplifiedParameter != 
									addNegation(parameters[i], isNegated)) {
								parameterSimplified = true;
							}
							newParameters.add(simplifiedParameter);
						}
						
					}
					if (parameterSimplified) {
						break;
//						parameters = new Term[newParameters.size()];
//						int k = 0;
//						for (Term t : newParameters) {
//							parameters[k] = t;
//							k++;
//						}
//						newParameters.clear();
//						connective = isAnd ? "and" : "or";
//						isNegated = false;
					}
				}
				// if a parameter was simplified
				if (parameterSimplified) {
					// Building the return term
					Term[] newParametersAsArray = 
							newParameters.toArray(new Term[newParameters.size()]);
					if (isAnd) {
						return Util.and(m_Script, newParametersAsArray);
					} else {
						return Util.or(m_Script, newParametersAsArray);
					}
				}
				// no parameter could be simplified so return the input term
				else {
					return addNegation(inputTerm, isNegated);
				}
				
			}
		}
		Term realInput = addNegation(inputTerm, isNegated);
		Redundancy redundancy = this.getRedundancy(realInput);
		switch (redundancy) {
				case NON_CONSTRAINING: return m_True;
				case NON_RELAXING: return m_False;
				default: return realInput;
		}
	}
	
}
