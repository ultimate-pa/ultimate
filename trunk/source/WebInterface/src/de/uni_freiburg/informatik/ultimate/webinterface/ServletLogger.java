package de.uni_freiburg.informatik.ultimate.webinterface;

import javax.servlet.http.HttpServlet;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public class ServletLogger {

	private final HttpServlet mServlet;
	private final boolean mDebug;

	public ServletLogger(final HttpServlet servlet, final String id, final boolean debug) {
		mServlet = servlet;
		mDebug = debug;
	}

	public boolean isDebugEnabled() {
		return mDebug;
	}

	public void logDebug(String message) {
		if (mDebug && message != null) {
			String timestamp = CoreUtil.getCurrentDateTimeAsString();
			timestamp = "[" + timestamp + "][DEBUG] ";
			message = timestamp + message;
			System.out.println(message);
			mServlet.log(message);
		}
	}

	public void log(String message) {
		if (message != null) {
			String timestamp = CoreUtil.getCurrentDateTimeAsString();
			timestamp = "[" + timestamp + "] ";
			message = timestamp + message;
			System.out.println(message);
			mServlet.log(message);
		}
	}
}
