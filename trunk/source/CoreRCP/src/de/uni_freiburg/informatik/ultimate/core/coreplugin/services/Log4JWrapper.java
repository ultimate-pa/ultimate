package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public final class Log4JWrapper implements ILogger {

	private static final String FQCN = Log4JWrapper.class.getName();
	private final Logger mLogger;

	public Log4JWrapper(final Logger logger) {
		mLogger = logger;
	}

	Logger getBacking() {
		return mLogger;
	}

	@Override
	public boolean isFatalEnabled() {
		return Level.FATAL.isGreaterOrEqual(mLogger.getLevel());
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLogger.log(FQCN, Level.FATAL, msg, t);
	}

	@Override
	public void fatal(final Object msg) {
		mLogger.log(FQCN, Level.FATAL, msg, null);
	}

	@Override
	public boolean isErrorEnabled() {
		return Level.ERROR.isGreaterOrEqual(mLogger.getLevel());
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLogger.log(FQCN, Level.ERROR, msg, t);
	}

	@Override
	public void error(final Object msg) {
		mLogger.log(FQCN, Level.ERROR, msg, null);
	}

	@Override
	public boolean isWarnEnabled() {
		return Level.WARN.isGreaterOrEqual(mLogger.getLevel());
	}

	@Override
	public void warn(final Object msg) {
		mLogger.log(FQCN, Level.WARN, msg, null);
	}

	@Override
	public boolean isInfoEnabled() {
		return mLogger.isInfoEnabled();
	}

	@Override
	public void info(final Object msg) {
		mLogger.log(FQCN, Level.INFO, msg, null);
	}

	@Override
	public boolean isDebugEnabled() {
		return mLogger.isDebugEnabled();
	}

	@Override
	public void debug(final Object msg) {
		mLogger.log(FQCN, Level.DEBUG, msg, null);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mLogger == null) ? 0 : mLogger.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Log4JWrapper other = (Log4JWrapper) obj;
		if (mLogger == null) {
			if (other.mLogger != null) {
				return false;
			}
		} else if (!mLogger.equals(other.mLogger)) {
			return false;
		}
		return true;
	}
}