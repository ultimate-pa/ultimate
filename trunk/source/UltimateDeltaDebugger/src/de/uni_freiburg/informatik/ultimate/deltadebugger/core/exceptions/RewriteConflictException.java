package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown when several rewrite operations are conflicting, i.e. overlap the same
 * location.
 */
public class RewriteConflictException extends RuntimeException {

	public RewriteConflictException() {
		super();
	}

	public RewriteConflictException(String message, Throwable cause) {
		super(message, cause);
	}

	public RewriteConflictException(String message) {
		super(message);
	}

	public RewriteConflictException(Throwable cause) {
		super(cause);
	}

}