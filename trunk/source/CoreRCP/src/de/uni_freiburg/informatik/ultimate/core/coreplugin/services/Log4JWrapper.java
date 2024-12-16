/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class Log4JWrapper implements ILogger {

	private static final Level[] sILoggerLevelToLog4jLevel =
			{ Level.DEBUG, Level.INFO, Level.WARN, Level.ERROR, Level.FATAL, Level.OFF };

	private static final String FQCN = ILogger.class.getName();

	private final Logger mLogger;

	public Log4JWrapper(final Logger logger) {
		mLogger = logger;
	}

	Logger getBacking() {
		return mLogger;
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLogger.log(FQCN, Level.FATAL, msg, t);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLogger.log(FQCN, Level.ERROR, msg, t);
	}

	@Override
	public void log(final LogLevel level, final String msg) {
		mLogger.log(FQCN, translateLevel(level), msg, null);
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
		final Log4JWrapper other = (Log4JWrapper) obj;
		return Objects.equals(mLogger, other.mLogger);
	}

	@Override
	public String toString() {
		return "[" + hashCode() + "][" + getBacking().getLevel() + "] " + getBacking().getName();
	}

	@Override
	public void setLevel(final LogLevel level) {
		mLogger.setLevel(translateLevel(level));
	}

	@Override
	public boolean isLogLevelEnabled(final LogLevel level) {
		return mLogger.isEnabledFor(translateLevel(level));
	}

	private static Level translateLevel(final LogLevel level) {
		if (level.ordinal() >= sILoggerLevelToLog4jLevel.length) {
			throw new UnsupportedOperationException("Unknown LogLevel " + level);
		}
		return sILoggerLevelToLog4jLevel[level.ordinal()];
	}
}
