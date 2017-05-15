package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * Base Class for Exceptions the Server can throw
 * 
 * @author Julian Jarecki
 *
 */
public abstract class ServerException extends RuntimeException {
	private static final long serialVersionUID = -5783259998242495330L;

	public ServerException(final String string) {
		super(string);
	}
}
