package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

public class UnbalancedConditionalDirectiveException extends ParserException {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;

	public UnbalancedConditionalDirectiveException() {
		super();
	}

	public UnbalancedConditionalDirectiveException(final String message) {
		super(message);
	}

}
