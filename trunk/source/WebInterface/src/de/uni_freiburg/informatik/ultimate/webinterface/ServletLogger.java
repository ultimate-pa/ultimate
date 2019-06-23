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

	public void logDebug(final String message) {
		if (!mDebug || message == null) {
			return;
		}
		final String stampedMsg = "[" + CoreUtil.getCurrentDateTimeAsString() + "][DEBUG] " + message;
		mServlet.log(stampedMsg);
		System.out.println(stampedMsg);
	}

	public void log(final String message) {
		if (message == null) {
			return;
		}
		final String stampedMsg = "[" + CoreUtil.getCurrentDateTimeAsString() + "] " + message;
		mServlet.log(stampedMsg);
		System.out.println(stampedMsg);
	}

	public void logException(final String message, final Throwable t) {
		if (message == null) {
			return;
		}
		final String stampedMsg = "[" + CoreUtil.getCurrentDateTimeAsString() + "] " + message;
		mServlet.log(stampedMsg, t);
		System.out.println(stampedMsg + " " + t.toString());
	}
}
