package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

/**
 * This Exception is thrown, when a Client is sending a SORRY-Message,
 * indicating, that it does not Provide the functionality that Ultimate
 * expected.
 * 
 * @author Julian Jarecki
 *
 */
public class ClientQuittedException extends ClientException {
	private static final long serialVersionUID = -6661706136643107194L;
}
