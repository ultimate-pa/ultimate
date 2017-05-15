package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * Base Class for Exceptions that relate to the Client.
 * 
 * @author Julian Jarecki
 *
 */
public abstract class ClientException extends RuntimeException {
	private static final long serialVersionUID = -7083822127328710209L;

	public ClientException() {
	}

	public ClientException(final String message) {
		super(message);
	}
}
