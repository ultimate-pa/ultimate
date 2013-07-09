package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This is an abstract superclass of exceptions that occur when handling terms.
 * It carries an error message as well as a term instance.
 * 
 * @author Jan Leike
 */
public class TermException extends Exception {
	
	private static final long serialVersionUID = 628015504018345983L;
	
	protected Term m_term;
	
	public TermException(String description) {
		super(description);
		m_term = null;
	}
	
	public TermException(String description, Term term) {
		super(description);
		m_term = term;
	}
	
	/**
	 * @return the associated term
	 */
	public Term getTerm() {
		return m_term;
	}
	
	@Override
	public String toString() {
		if (m_term != null) {
			return super.toString() + " @term: " + m_term;
		} else {
			return super.toString();
		}
	}
}