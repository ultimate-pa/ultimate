/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.acsl.parser;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Exception class which is thrown by the ACSLParser
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.04.2012
 */
public class ACSLSyntaxErrorException extends Exception {

	/**
	 * ACSLNode that locates the SyntaxError.
	 */
	private ACSLNode location;

	/**
	 * The message of this Exception (is displayed to the user).
	 */
	private String message;

	/**
	 * SerialID
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructor
	 * 
	 * @param location dummyLocation of the Syntax-Error.
	 * @param message the message text of this exception.
	 */
	public ACSLSyntaxErrorException(ACSLNode location, String message) {
		this.location = location;
		this.message = message;
	}

	/**
	 * @return the location.
	 */
	public ACSLNode getLocation() {
		return location;
	}

	/**
	 * @return given message text.
	 */
	public String getMessageText() {
		return message;
	}
}
