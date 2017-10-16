/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.LoggerContext;
import org.apache.logging.log4j.core.config.Configuration;
import org.apache.logging.log4j.core.config.LoggerConfig;
import org.apache.logging.log4j.spi.ExtendedLogger;
import org.apache.logging.log4j.spi.ExtendedLoggerWrapper;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Wrapper class for Log4J2Loggers.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class Log4J2Wrapper implements ILogger {

	private static final String FQCN = Log4J2Wrapper.class.getName();
	private final ExtendedLoggerWrapper mLogger;

	public Log4J2Wrapper(final Logger logger) {
		mLogger = new ExtendedLoggerWrapper((ExtendedLogger) logger, logger.getName(), logger.getMessageFactory());

	}

	Logger getBacking() {
		return mLogger;
	}

	@Override
	public boolean isFatalEnabled() {
		return mLogger.isFatalEnabled();
		// return Level.FATAL.isLessSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isErrorEnabled() {
		return mLogger.isErrorEnabled();
		// return Level.ERROR.isLessSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isWarnEnabled() {
		return mLogger.isWarnEnabled();
		// return Level.WARN.isLessSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isInfoEnabled() {
		return mLogger.isInfoEnabled();
	}

	@Override
	public boolean isDebugEnabled() {
		return mLogger.isDebugEnabled();
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLogger.logIfEnabled(FQCN, Level.FATAL, null, msg, t);
	}

	@Override
	public void fatal(final Object msg) {
		mLogger.logIfEnabled(FQCN, Level.FATAL, null, msg, null);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLogger.logIfEnabled(FQCN, Level.ERROR, null, msg, t);
	}

	@Override
	public void error(final Object msg) {
		mLogger.logIfEnabled(FQCN, Level.ERROR, null, msg, null);
	}

	@Override
	public void warn(final Object msg) {
		mLogger.logIfEnabled(FQCN, Level.WARN, null, msg, null);
	}

	@Override
	public void info(final Object msg) {
		mLogger.logIfEnabled(FQCN, Level.INFO, null, msg, null);
	}

	@Override
	public void debug(final Object msg) {
		mLogger.logIfEnabled(FQCN, Level.DEBUG, null, msg, null);
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
		final Log4J2Wrapper other = (Log4J2Wrapper) obj;
		if (mLogger == null) {
			if (other.mLogger != null) {
				return false;
			}
		} else if (!mLogger.equals(other.mLogger)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "[" + hashCode() + "][" + getBacking().getLevel() + "] " + getBacking().getName();
	}

	@Override
	public void setLevel(final LogLevel level) {

		final Level log4j2Level;
		switch (level) {
		case DEBUG:
			log4j2Level = Level.DEBUG;
			break;
		case ERROR:
			log4j2Level = Level.ERROR;
			break;
		case FATAL:
			log4j2Level = Level.FATAL;
			break;
		case INFO:
			log4j2Level = Level.INFO;
			break;
		case OFF:
			log4j2Level = Level.OFF;
			break;
		case WARN:
			log4j2Level = Level.WARN;
			break;
		default:
			throw new UnsupportedOperationException("Unhandled LogLevel " + level);
		}

		final LoggerContext ctx = (LoggerContext) LogManager.getContext(false);
		final Configuration config = ctx.getConfiguration();
		final LoggerConfig loggerConfig = config.getLoggerConfig(mLogger.getName());
		loggerConfig.setLevel(log4j2Level);
	}

}
