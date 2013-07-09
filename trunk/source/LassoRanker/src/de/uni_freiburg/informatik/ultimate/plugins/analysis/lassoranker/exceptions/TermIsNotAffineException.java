package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This type of exception is raised when processing a term which contains
 * non-linear operations.
 * 
 * @author Jan Leike
 */
public class TermIsNotAffineException extends TermException {
	
	private static final long serialVersionUID = 173432306044797947L;
	
	public TermIsNotAffineException(String description) {
		super(description);
	}
	
	public TermIsNotAffineException(String description, Term term) {
		super(description, term);
	}
}