package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * Base Class for Exceptions that relate to the Client.
 * 
 * @author Julian Jarecki
 *
 */
public abstract class ClientException extends RuntimeException {
	public ClientException() {
	}
	
	public ClientException(String message) {
		super(message);
	}

	private static final long serialVersionUID = -7083822127328710209L;
}
