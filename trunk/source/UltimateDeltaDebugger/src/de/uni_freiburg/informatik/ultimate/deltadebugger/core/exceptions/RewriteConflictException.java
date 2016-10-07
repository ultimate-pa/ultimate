package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown when several rewrite operations are conflicting, i.e. overlap the same location.
 */
public class RewriteConflictException extends RuntimeException {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public RewriteConflictException() {
		super();
	}

	public RewriteConflictException(final String message) {
		super(message);
	}

	public RewriteConflictException(final String message, final Throwable cause) {
		super(message, cause);
	}

	public RewriteConflictException(final Throwable cause) {
		super(cause);
	}

}