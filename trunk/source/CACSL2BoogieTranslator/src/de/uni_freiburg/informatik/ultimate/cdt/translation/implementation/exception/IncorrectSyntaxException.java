/**
 * The exception, which is thrown if the specified syntax is incorrect.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception;

/**
 * @author Markus Lindenmann
 * @since 26.04.2012
 */
public class IncorrectSyntaxException extends IllegalArgumentException {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -1309056833732436476L;

	/**
	 * Constructs an IncorrectSyntaxException with the specified detail
	 * message. Parameters:
	 * 
	 * @param msg
	 *            the detail message
	 */
	public IncorrectSyntaxException(final String msg) {
		super(msg);
	}
}
