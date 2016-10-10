package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown to indicate that anaylzing the input was not possible and no further variants can be generated.
 */
public class ParserException extends RuntimeException {
	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public ParserException() {
		super();
	}

	public ParserException(final String message) {
		super(message);
	}

	public ParserException(final String message, final Throwable cause) {
		super(message, cause);
	}

	public ParserException(final Throwable cause) {
		super(cause);
	}
}
