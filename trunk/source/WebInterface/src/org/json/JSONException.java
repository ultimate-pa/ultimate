package org.json;

/**
 * The JSONException is thrown by the JSON.org classes when things are amiss.
 * 
 * @author JSON.org
 * @version 2010-12-24
 */
public class JSONException extends Exception {
	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = 0;
	/**
	 * The cause for the exception.
	 */
	private Throwable cause;

	/**
	 * Constructs a JSONException with an explanatory message.
	 * 
	 * @param message
	 *            Detail about the reason for the exception.
	 */
	public JSONException(String message) {
		super(message);
	}

	/**
	 * Constructor.
	 * 
	 * @param cause
	 *            the cause for the exception.
	 */
	public JSONException(Throwable cause) {
		super(cause.getMessage());
		this.cause = cause;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Throwable#getCause()
	 */
	@Override
	public Throwable getCause() {
		return cause;
	}
}
