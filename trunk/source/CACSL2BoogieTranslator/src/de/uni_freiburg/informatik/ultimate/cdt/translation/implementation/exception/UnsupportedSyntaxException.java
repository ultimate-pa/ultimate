/**
 * The exception, which is thrown if the compiler does not yet support a specific syntax.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception;

/**
 * @author Markus Lindenmann
 * @since 26.04.2012
 */
public class UnsupportedSyntaxException extends UnsupportedOperationException {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -868222134936145470L;

	/**
	 * Constructs an UnsupportedSyntaxException with the specified detail
	 * message. Parameters:
	 * 
	 * @param msg
	 *            the detail message
	 */
	public UnsupportedSyntaxException(final String msg) {
		super(msg);
	}
}
