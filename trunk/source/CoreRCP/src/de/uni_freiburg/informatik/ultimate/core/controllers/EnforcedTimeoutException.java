package de.uni_freiburg.informatik.ultimate.core.controllers;


/**
 * Use this exception to signal that Ultimate was terminated trhough an external
 * timeout and is almost always in an unstable state.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class EnforcedTimeoutException extends RuntimeException {

	private static final long serialVersionUID = -6577471260294280323L;

	public EnforcedTimeoutException(String arg0) {
		super(arg0);
	}

}
