package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

public class MissingTestResultException extends RuntimeException {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public MissingTestResultException() {
		super();
	}

	public MissingTestResultException(final String message) {
		super(message);
	}

}
