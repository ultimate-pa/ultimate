package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Wraps an InterruptedException in an unchecked exception at places where it is unexpected and just as useful as an
 * arbitrary RuntimeException.
 */
public class UncheckedInterruptedException extends RuntimeException {
	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public UncheckedInterruptedException(final InterruptedException cause) {
		super(cause);
	}
}
