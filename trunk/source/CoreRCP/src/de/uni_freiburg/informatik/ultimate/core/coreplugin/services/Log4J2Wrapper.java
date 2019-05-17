/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2016,2019 University of Freiburg
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

import java.util.Objects;

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

	private static final Level[] sILoggerLevelToLog4jLevel = {
			Level.DEBUG, Level.INFO, Level.WARN, Level.ERROR, Level.FATAL, Level.OFF };

	private static final String FQCN = Log4J2Wrapper.class.getName();

	private final ExtendedLoggerWrapper mLogger;

	public Log4J2Wrapper(final Logger logger) {
		mLogger = new ExtendedLoggerWrapper((ExtendedLogger) logger, logger.getName(), logger.getMessageFactory());

	}

	Logger getBacking() {
		return mLogger;
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLogger.logIfEnabled(FQCN, Level.FATAL, null, msg, t);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLogger.logIfEnabled(FQCN, Level.ERROR, null, msg, t);
	}

	@Override
	public void log(final LogLevel level, final String msg) {
		mLogger.logIfEnabled(FQCN, translateLevel(level), null, msg);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mLogger);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		Log4J2Wrapper other = (Log4J2Wrapper) obj;
		return Objects.equals(mLogger, other.mLogger);
	}

	@Override
	public String toString() {
		return "[" + hashCode() + "][" + getBacking().getLevel() + "] " + getBacking().getName();
	}

	@Override
	public void setLevel(final LogLevel level) {
		final LoggerContext ctx = (LoggerContext) LogManager.getContext(false);
		final Configuration config = ctx.getConfiguration();
		final LoggerConfig loggerConfig = config.getLoggerConfig(mLogger.getName());
		loggerConfig.setLevel(translateLevel(level));
	}

	@Override
	public boolean isLogLevelEnabled(final LogLevel level) {
		return mLogger.isEnabled(translateLevel(level));
		// return translateLevel(level).isLessSpecificThan(mLogger.getLevel()); // comment from Marius Greitschus
	}

	private static Level translateLevel(final ILogger.LogLevel level) {
		if (level.ordinal() >= sILoggerLevelToLog4jLevel.length) {
			throw new UnsupportedOperationException("Unknown LogLevel " + level);
		}
		return sILoggerLevelToLog4jLevel[level.ordinal()];
	}
}
