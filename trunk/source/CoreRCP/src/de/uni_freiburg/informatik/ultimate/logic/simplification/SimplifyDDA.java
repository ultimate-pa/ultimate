package de.uni_freiburg.informatik.ultimate.logic.simplification;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
				String connective) throws SMTLIBException {
		// first we take the criticalConstraint of the parent
		Term criticalConstraint = criticalConstraintOfParent;
		if (connective == "and") {
			// here we add all siblings which are > i
			for (int j = positionI + 1; j < parameters.length; j++){
				criticalConstraint = Util.and(m_Script, 
						criticalConstraint, parameters[j]);
			}
			// here we add the siblings which have already been 
			// simplified.
			for (Term t : newParameters) {
				criticalConstraint = Util.and(m_Script, 
						criticalConstraint, t);
			}
			
		}
		if (connective == "or") {
			// here we add all siblings which are > i
			for (int j = positionI + 1; j < parameters.length; j++){
				criticalConstraint = Util.and(m_Script, criticalConstraint, 
						Util.not(m_Script, parameters[j]));
			}
			// here we add the siblings which have already been 
			// simplified.
			for (Term t : newParameters) {
				criticalConstraint = Util.and(m_Script, criticalConstraint, 
						Util.not(m_Script, t));
			}
		}
		return criticalConstraint;
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
		m_Logger.debug("Simplifying " + term);
		term = (new NegationNormalForm(m_Script)).getNNF(term);
		return this.getSimplifiedTerm(term, m_Script.term("true"));
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
	private Term getSimplifiedTerm(Term inputTerm, Term criticalConstraint)
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
			
			if (connective == "and" || connective == "or") {
				while (parameterSimplified) {
					parameterSimplified = false;
					for ( int i = 0; i < parameters.length; i++) {
						// first compute critical constraint
						Term criticalConstrainti = 
								this.computeCriticalConstraint
								(criticalConstraint, parameters, i, 
										newParameters, connective);
						// recursive call
						Term simplifiedParameter = this.getSimplifiedTerm(
								parameters[i], criticalConstrainti);
						if (simplifiedParameter != parameters[i]) {
							parameterSimplified = true;
							inputParameterSimplified = true;
						}
						if (connective == "and") {
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
						}
						if (connective == "or") {
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
						parameters = new Term[newParameters.size()];
						int k = 0;
						for (Term t : newParameters) {
							parameters[k] = t;
							k++;
						}
						newParameters.clear();
						
					}
				}
				// if a parameter was simplified
				if (inputParameterSimplified) {
					// Building the return term
					Term[] newParametersAsArray =
							new Term[newParameters.size()];
					int j = 0;
					for (Term t : newParameters) {
						newParametersAsArray[j] = t;
						j++;
					}
					if (j == 0) {
						if (connective == "and") {
							return m_Script.term("true");
						}
						if (connective == "or") {
							return m_Script.term("false");
						}
					}
					// if there was only 1 term return it
					if (j == 1){
						return newParametersAsArray[0];
					}
					// if there were more than 1 term, return the conjunction
					// if connective was and
					if (connective == "and") {
						return Util.and(m_Script, newParametersAsArray);
					}
					
					if (connective == "or") {
						return Util.or(m_Script, newParametersAsArray);
					}
				}
				// no parameter could be simplified so return the input term
				else {
					return inputTerm;
				}
				
			}
		}
		Redundancy redundancy = this.getRedundancy(inputTerm, 
															criticalConstraint);
		switch (redundancy) {
				case NON_CONSTRAINING: return m_Script.term("true");
				case NON_RELAXING: return m_Script.term("false");
				default: return inputTerm;
		}
	}
	
}
