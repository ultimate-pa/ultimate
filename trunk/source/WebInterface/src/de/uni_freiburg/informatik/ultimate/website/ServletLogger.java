package de.uni_freiburg.informatik.ultimate.website;

import javax.servlet.http.HttpServlet;

public class ServletLogger {

	private final HttpServlet mServlet;
	private final boolean mDebug;

	public ServletLogger(HttpServlet servlet, boolean debug) {
		mServlet = servlet;
		mDebug = debug;
	}

	public void logDebug(String message) {
		if (mDebug && message !=null) {
			mServlet.log(message);
			System.out.println(message);
		}
	}
}
