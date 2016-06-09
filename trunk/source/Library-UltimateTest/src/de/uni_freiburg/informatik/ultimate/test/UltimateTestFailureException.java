package de.uni_freiburg.informatik.ultimate.test;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateTestFailureException extends AssertionError {

	private static final long serialVersionUID = 1L;

	public UltimateTestFailureException(final String message) {
		super(message);
	}

	public UltimateTestFailureException(final String message, final Throwable th) {
		super(message, th);
	}
}
