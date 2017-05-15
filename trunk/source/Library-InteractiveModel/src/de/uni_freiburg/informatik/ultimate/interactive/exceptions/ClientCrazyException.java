package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * This Exception is thrown, when a Client appears to have violated the Ultimate
 * Interactive Protocol.
 * 
 * @author Julian Jarecki
 *
 */
public class ClientCrazyException extends ClientException {
	private static final long serialVersionUID = 6163598721264845950L;
	
	public ClientCrazyException(final String message) {
		super(message);
	}
}
