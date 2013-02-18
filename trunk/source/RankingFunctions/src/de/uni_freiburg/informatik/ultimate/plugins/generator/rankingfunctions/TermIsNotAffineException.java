package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This type of exception is raised if an attempt is made to convert
 * a term which is not affine into an instance of the class AffineTerm.
 * 
 * @author Jan Leike
 */
public class TermIsNotAffineException extends Exception {
	
	private static final long serialVersionUID = 173432306044797947L;
	
	private String m_description;
	private Term m_term;
	
	public TermIsNotAffineException() {
		m_description = "";
		m_term = null;
	}
	
	public TermIsNotAffineException(String description) {
		m_description = description;
		m_term = null;
	}
	
	public TermIsNotAffineException(String description, Term term) {
		m_description = description;
		m_term = term;
	}
	
	public String getDescription() {
		return m_description;
	}
	
	public Term getTerm() {
		return m_term;
	}
	
	@Override
	public String toString() {
		return m_description + " @term: " + m_term;
	}
}