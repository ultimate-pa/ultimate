package de.uni_freiburg.informatik.ultimate.logic.simplification;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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
	
	/**
	 * The constructor gets the script interface and the logger for output
	 */
	public SimplifyDDA(final Script script, final Logger logger) 
			throws SMTLIBException {
		m_Script = script;
		m_Logger = logger;
	}
	
	/**
	 * Redundancy is a property of a subterm B with respect to its term A.
	 * The subterm B is called:
	 * <ul>
	 * <li> NON_REAXING if term A is equivalent to the term, where B is replaced
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
	 * Checks if term is redundant, with respect to its critical constraint.
	 */
	private Redundancy getRedundancy (Term term, Term criticalConstraint)
			throws SMTLIBException {
		Term nonConstrainingTestTerm = Util.implies(m_Script, criticalConstraint,
				term);
		LBool isTermConstraining =
				Util.checkSat(m_Script, Util.not(m_Script,nonConstrainingTestTerm));
		if (isTermConstraining == LBool.UNSAT) {
//			m_Logger.debug(nonConstrainingTestTerm + " is valid");
			return Redundancy.NON_CONSTRAINING;
		}
				
		Term nonRelaxingTestTerm = Util.implies(m_Script, criticalConstraint,
				Util.not(m_Script, term));
		LBool isTermRelaxing = 
				Util.checkSat(m_Script, Util.not(m_Script,nonRelaxingTestTerm));
		if (isTermRelaxing == LBool.UNSAT) {
//			m_Logger.debug(nonRelaxingTestTerm + " is valid");
			return Redundancy.NON_RELAXING;
		}
		
		return Redundancy.NOT_REDUNDANT;
	}
	
	/**
	 *  Get the critical constraint of a node or leave in the treestructure 
	 *  reprensantation of a term.
	 *  Computes the critical constraint using the critical constraint of the 
	 *  parent and all its siblings, which are stored in the parameters array.
	 *  positionI is used to remember at which parameters we have already looked
	 *  at. To get all siblings we take all terms in parameters with position
	 *  greater than positionI and all terms from newParameters, the ones
	 *  already simplified.
	 */
	private Term computeCriticalConstraint(Term criticalConstraintOfParent,
			Term[] parameters, int positionI, HashSet<Term> newParameters,
				String connective, boolean isNegated) throws SMTLIBException {
		// first we take the criticalConstraint of the parent
		Term criticalConstraint = criticalConstraintOfParent;
		// Is this a conjunctive context?
		boolean isAnd = (connective == "and") != isNegated; 
		// In an conjunctive context, the critical context is just the conjunction
		// of all siblings.  These need to hold for the children to be relevant.
		//
		// In a disjunctive context, the critical context is the conjunction of
		// the negation of all siblings.  All siblings must be false for the
		// formula to be relevant.
		
		// here we add all siblings which are > i
		for (int j = positionI + 1; j < parameters.length; j++){
			boolean paramNegated = isNegated != (connective == "=>" && j < parameters.length - 1); 			
			criticalConstraint = Util.and(m_Script, 
					criticalConstraint, addNegation(parameters[j], isAnd == paramNegated));
		}
		// here we add the siblings which have already been 
		// simplified.
		for (Term t : newParameters) {
			criticalConstraint = Util.and(m_Script, 
					criticalConstraint, addNegation(t, !isAnd));
		}
		return criticalConstraint;
	}
	
	private Term addNegation(Term t, boolean isNegated) {
		if (isNegated)
			return Util.not(m_Script, t);
		else
			return t;
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
	public Term getSimplifiedTerm(Term term) throws SMTLIBException {
//		m_Logger.debug("Simplifying " + term);
		term = new FormulaUnLet().unlet(term);
		term = this.getSimplifiedTerm(term, m_Script.term("true"), false);
		m_Logger.debug("Simplified to: " + term);
		return term;
	}
	

	/**
	 * If no subterm of inputTerm is redundant with respect criticalConstraint,
	 * return inputTerm.
	 * Otherwise return a copy of inputTerm where each subterm which is 
	 * NON_CONSTRAINING wrt. criticalConstraint is replaced by true and
	 * each subterm which is NON_RELAXING wrt. criticalConstraint is replaced by
	 * false.
	 * @param inputTerm term whose Sort is Boolean
	 * @param criticalConstraint whose Sort is Boolean
	 */
	private Term getSimplifiedTerm(Term inputTerm, Term criticalConstraint, boolean isNegated)
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
			Boolean inputParameterSimplified = false;
			
			if (connective == "not")
				return this.getSimplifiedTerm(parameters[0], criticalConstraint, !isNegated);
			if (connective == "ite") {
				Term cond = this.getSimplifiedTerm(parameters[0], criticalConstraint, false);
				Term simpThen = this.getSimplifiedTerm(parameters[1], Util.and(m_Script, criticalConstraint, cond), isNegated);
				Term simpElse = this.getSimplifiedTerm(parameters[2], Util.and(m_Script, criticalConstraint, Util.not(m_Script, cond)), isNegated);
				Term trueTerm = m_Script.term("true");
				Term falseTerm = m_Script.term("false");
				if (cond == trueTerm) return simpThen;
				else if (cond == falseTerm) return simpElse;
				else if (simpThen == trueTerm) return Util.or(m_Script, cond, simpElse);
				else if (simpElse == falseTerm) return Util.and(m_Script, cond, simpThen);
				else if (simpThen == falseTerm) return Util.and(m_Script, Util.not(m_Script, cond), simpElse);
				else if (simpElse == trueTerm) return Util.or(m_Script, Util.not(m_Script, cond), simpThen);
				return m_Script.term("ite", cond, simpThen, simpElse);
			}
			if (connective == "and" || connective == "or" || connective == "=>") {
				boolean isAnd = (connective == "and") != isNegated; 
				while (parameterSimplified) {
					parameterSimplified = false;
					for ( int i = 0; i < parameters.length; i++) {
						boolean paramNegated = isNegated != (connective == "=>" && i < parameters.length - 1); 
						Term parami = addNegation(parameters[i], paramNegated);
						if (newParameters.contains(parami)) {
							parameterSimplified = true;
							inputParameterSimplified = true;
							continue;
						}
						// first compute critical constraint
						Term criticalConstrainti = 
								this.computeCriticalConstraint
								(criticalConstraint, parameters, i, 
										newParameters, connective, isNegated);
						// recursive call
						Term simplifiedParameter = this.getSimplifiedTerm(
								parameters[i], criticalConstrainti, paramNegated);
						if (simplifiedParameter != parami) {
							parameterSimplified = true;
							inputParameterSimplified = true;
						}
						if (isAnd) {
							if (simplifiedParameter == m_Script.term("true")) {
								inputParameterSimplified = true;
								parameterSimplified = true;
							}
							else if (simplifiedParameter ==
														m_Script.term("false")){
								inputParameterSimplified = true;
								parameterSimplified = true;
								return m_Script.term("false");
							}
							else {
								newParameters.add(simplifiedParameter);
							}
						} else {
							if (simplifiedParameter == m_Script.term("true")) {
								inputParameterSimplified = true;
								parameterSimplified = true;
								return m_Script.term("true");
							}
							else if (simplifiedParameter == 
														m_Script.term("false")){
								inputParameterSimplified = true;
								parameterSimplified = true;
							}
							else {
								newParameters.add(simplifiedParameter);
							}
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
				if (inputParameterSimplified) {
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
		Redundancy redundancy = this.getRedundancy(realInput, 
													criticalConstraint);
		switch (redundancy) {
				case NON_CONSTRAINING: return m_Script.term("true");
				case NON_RELAXING: return m_Script.term("false");
				default: return realInput;
		}
	}
	
}
