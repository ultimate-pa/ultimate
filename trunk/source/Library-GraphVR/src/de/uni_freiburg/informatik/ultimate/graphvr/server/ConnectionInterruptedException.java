package de.uni_freiburg.informatik.ultimate.graphvr.server;

public class ConnectionInterruptedException extends Exception {
	private Throwable mException;

	public ConnectionInterruptedException(Throwable e) {
		this.mException = e;
	}

	public Throwable getException() {
		return mException;
	}
}
