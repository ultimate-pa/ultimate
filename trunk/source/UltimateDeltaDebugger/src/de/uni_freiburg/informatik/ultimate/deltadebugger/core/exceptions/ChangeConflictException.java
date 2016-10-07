package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown to indicate that one or multie changes could not be applied. The caller can continue to generate other
 * variants, just this particular combination of changes is possible to apply.
 */
public class ChangeConflictException extends RuntimeException {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public ChangeConflictException() {
		super();
	}

	public ChangeConflictException(final String message) {
		super(message);
	}

	public ChangeConflictException(final String message, final Throwable cause) {
		super(message, cause);
	}

	public ChangeConflictException(final String message, final Throwable cause, final boolean enableSuppression,
			final boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}

	public ChangeConflictException(final Throwable cause) {
		super(cause);
	}

}