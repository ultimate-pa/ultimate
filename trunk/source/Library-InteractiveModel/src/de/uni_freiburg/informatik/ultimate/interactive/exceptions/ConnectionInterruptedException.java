package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

public class ConnectionInterruptedException extends Exception {
	private static final long serialVersionUID = -6019449476228529921L;

	public ConnectionInterruptedException(final Throwable cause) {
		super(cause);
	}
}
