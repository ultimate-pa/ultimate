package de.uni_freiburg.informatik.ultimate.util;

/**
 * Exception that can be thrown if a plugin detects that the timeout is overdue
 * or a canellation of the toolchain was requested.
 *
 */
public class OperationCanceledException extends RuntimeException {
	
	private static final long serialVersionUID = 7090759880566576629L;
	
	private final static String s_Message = "Timout or Toolchain cancelled by user";

	public OperationCanceledException() {
		super(s_Message);
	}

	@Override
	public String getMessage() {
		return super.getMessage();
	}

	
}
