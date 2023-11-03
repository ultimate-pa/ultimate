package de.uni_freiburg.informatik.ultimate.web.backend.util;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Objects;

import javax.servlet.http.HttpServlet;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public class ServletLogger implements ILogger {

	private final HttpServlet mServlet;
	private LogLevel mLogLevel;

	public ServletLogger(final HttpServlet servlet, final boolean debug) {
		mServlet = servlet;
		if (debug) {
			mLogLevel = LogLevel.DEBUG;
		} else {
			mLogLevel = LogLevel.INFO;
		}
	}

	private static String addTimestamp(final LogLevel level, final String msg) {
		return String.format("[%s][%s] %s", CoreUtil.getCurrentDateTimeAsString(), level, msg);
	}

	private static String throwableToString(final Throwable t) {
		if (t == null) {
			return Objects.toString(t);
		}
		final StringWriter sw = new StringWriter();
		final PrintWriter pw = new PrintWriter(sw);
		t.printStackTrace(pw);
		sw.flush();
		return sw.toString();
	}

	private static String objectToString(final Object msg) {
		if (msg instanceof String) {
			return (String) msg;
		}
		return Objects.toString(msg);
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		log(LogLevel.FATAL, "%s %s", objectToString(msg), throwableToString(t));
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		log(LogLevel.ERROR, "%s %s", objectToString(msg), throwableToString(t));

	}

	@Override
	public boolean isLogLevelEnabled(final LogLevel level) {
		return level.ordinal() >= mLogLevel.ordinal();
	}

	@Override
	public void log(final LogLevel level, final String message) {
		mServlet.log(addTimestamp(level, message));
	}

	@Override
	public void setLevel(final LogLevel level) {
		mLogLevel = level;
	}

}
