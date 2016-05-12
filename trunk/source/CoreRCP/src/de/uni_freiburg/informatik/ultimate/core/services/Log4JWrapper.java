package de.uni_freiburg.informatik.ultimate.core.services;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

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
		return mLogger.getLevel().isGreaterOrEqual(Level.FATAL);
	}

	@Override
	public void fatal(Object msg, Throwable t) {
		mLogger.log(FQCN, Level.FATAL, msg, t);
	}

	@Override
	public void fatal(Object msg) {
		mLogger.log(FQCN, Level.FATAL, msg, null);
	}

	@Override
	public boolean isErrorEnabled() {
		return mLogger.getLevel().isGreaterOrEqual(Level.ERROR);
	}

	@Override
	public void error(Object msg, Throwable t) {
		mLogger.log(FQCN, Level.ERROR, msg, t);
	}

	@Override
	public void error(Object msg) {
		mLogger.log(FQCN, Level.ERROR, msg, null);
	}

	@Override
	public boolean isWarnEnabled() {
		return mLogger.getLevel().isGreaterOrEqual(Level.WARN);
	}

	@Override
	public void warn(Object msg) {
		mLogger.log(FQCN, Level.WARN, msg, null);
	}

	@Override
	public boolean isInfoEnabled() {
		return mLogger.isInfoEnabled();
	}

	@Override
	public void info(Object msg) {
		mLogger.log(FQCN, Level.INFO, msg, null);
	}

	@Override
	public boolean isDebugEnabled() {
		return mLogger.isDebugEnabled();
	}

	@Override
	public void debug(Object msg) {
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
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Log4JWrapper other = (Log4JWrapper) obj;
		if (mLogger == null) {
			if (other.mLogger != null)
				return false;
		} else if (!mLogger.equals(other.mLogger))
			return false;
		return true;
	}
}