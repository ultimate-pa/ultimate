package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Wraps an InterruptedException in an unchecked exception at places where it is
 * unexpected and just as useful as an arbitrary RuntimeException.
 */
public class UncheckedInterruptedException extends RuntimeException {
	public UncheckedInterruptedException(InterruptedException cause) {
		super(cause);
	}
}
