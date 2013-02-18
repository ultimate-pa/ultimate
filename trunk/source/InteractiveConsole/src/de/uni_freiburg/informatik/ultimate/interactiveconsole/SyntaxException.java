package de.uni_freiburg.informatik.ultimate.interactiveconsole;

public class SyntaxException extends Exception {
	private static final long serialVersionUID = -1315134290943693785L;

	public SyntaxException() {
	}

	public SyntaxException(String message) {
		super(message);
	}

	public SyntaxException(Throwable cause) {
		super(cause);
	}

	public SyntaxException(String message, Throwable cause) {
		super(message, cause);
	}

}
