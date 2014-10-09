package de.uni_freiburg.informatik.ultimate.core.controllers;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;

/**
 * Use this exception to signal that Ultimate encountered a serious error before
 * it could call {@link IController#init(ICore, ILoggingService)}
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class LivecycleException extends RuntimeException {

	private static final long serialVersionUID = -6577471260294280323L;

	public LivecycleException(String arg0) {
		super(arg0);
	}

}
