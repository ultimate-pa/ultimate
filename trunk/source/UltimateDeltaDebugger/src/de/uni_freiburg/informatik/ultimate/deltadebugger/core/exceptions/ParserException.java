package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown to indicate that anaylzing the input was not possible and no further
 * variants can be generated.
 */
public class ParserException extends RuntimeException {
	public ParserException() {
		super();
	}

	public ParserException(String message, Throwable cause) {
		super(message, cause);
	}

	public ParserException(String message) {
		super(message);
	}

	public ParserException(Throwable cause) {
		super(cause);
	}
}
