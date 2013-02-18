/**
 * The exception, which is thrown if the specified code contains type errors.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception;

/**
 * @author Markus Lindenmann
 * @since 26.04.2012
 */
public class TypeErrorException extends IllegalArgumentException {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -4051869990676408444L;

	/**
	 * Constructs an TypeErrorException with the specified detail
	 * message. Parameters:
	 * 
	 * @param msg
	 *            the detail message
	 */
	public TypeErrorException(final String msg) {
		super(msg);
	}
}
