package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown to indicate that one or multie changes could not be applied. The
 * caller can continue to generate other variants, just this particular
 * combination of changes is possible to apply.
 */
public class ChangeConflictException extends RuntimeException {

	public ChangeConflictException() {
		super();
	}

	public ChangeConflictException(String message, Throwable cause, boolean enableSuppression,
			boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}

	public ChangeConflictException(String message, Throwable cause) {
		super(message, cause);
	}

	public ChangeConflictException(String message) {
		super(message);
	}

	public ChangeConflictException(Throwable cause) {
		super(cause);
	}
	
}