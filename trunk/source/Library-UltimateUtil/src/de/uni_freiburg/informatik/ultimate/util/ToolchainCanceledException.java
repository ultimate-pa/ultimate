package de.uni_freiburg.informatik.ultimate.util;

/**
 * Exception that can be thrown if a plugin detects that the timeout is overdue
 * or a cancellation of the toolchain was requested.
 * 
 * The core will create TimeoutResult if this exception is thrown. 
 *
 */
public class ToolchainCanceledException extends RuntimeException {
	
	private static final long serialVersionUID = 7090759880566576629L;
	
	public final static String s_Message = "Timeout or Toolchain cancelled by user";
	private final Class<?> m_ClassOfThrower; 
	private final String m_WhatWasGoingOnMessage;

	public ToolchainCanceledException(Class<?> thrower) {
		super(s_Message);
		m_ClassOfThrower = thrower;
		m_WhatWasGoingOnMessage = null;
	}
	
	public ToolchainCanceledException(Class<?> thrower, String whatWasGoingOnMessage) {
		super(s_Message);
		m_ClassOfThrower = thrower;
		m_WhatWasGoingOnMessage = whatWasGoingOnMessage;
	}

	@Override
	public String getMessage() {
		return super.getMessage();
	}
	
	/**
	 * Get the class of the object that has thrown this Exception.
	 * @return
	 */
	public Class<?> getClassOfThrower() {
		return m_ClassOfThrower;
	}

	/**
	 * Return optional message that was added by the algorithm that has
	 * thrown this Exception. Null if no optional Message was provided.
	 */
	public String getWhatWasGoingOnMessage() {
		return m_WhatWasGoingOnMessage;
	}
	
	
}
