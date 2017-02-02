package de.uni_freiburg.informatik.ultimate.server.exceptions;

public class ConnectionInterruptedException extends Exception {
	private Throwable mException;

	public ConnectionInterruptedException(Throwable e) {
		this.mException = e;
	}

	public Throwable getException() {
		return mException;
	}
}
