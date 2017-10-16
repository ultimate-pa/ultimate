/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.model.services;

import java.util.Enumeration;

/**
 * Ultiamte's logging interface. It is similar to the old log4j API, but it should get smaller over time (i.e., methods
 * throwing exceptions will be removed in time).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface ILogger {

	/**
	 * Log levels supported by {@link ILogger}. The order of the constants is from most logging to least logging.
	 * {@link LogLevel#DEBUG} is currently the lowest level (logs the most).
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum LogLevel {
		/**
		 * Logs all log messages of level {@link #DEBUG} and above.
		 */
		DEBUG,
		/**
		 * Log all log messages of level {@link #INFO} and above.
		 */
		INFO,
		/**
		 * Log all log messages of level {@link #WARN} and above.
		 */
		WARN,
		/**
		 * Log all log messages of level {@link #ERROR} and above.
		 */
		ERROR,
		/**
		 * Log all log messages of level {@link #FATAL} and above.
		 */
		FATAL,
		/**
		 * Disable logging by this logger.
		 */
		OFF
	}

	boolean isFatalEnabled();

	void fatal(Object msg, Throwable t);

	void fatal(Object msg);

	boolean isErrorEnabled();

	void error(Object msg, Throwable t);

	void error(Object msg);

	boolean isWarnEnabled();

	void warn(Object msg);

	boolean isInfoEnabled();

	void info(Object msg);

	boolean isDebugEnabled();

	void debug(Object msg);

	/**
	 * Sets this logger to a level specified by {@link LogLevel}. Only messages matching this level are logged.
	 *
	 * @param level
	 *            The level this logger should be set to.
	 */
	void setLevel(final LogLevel level);

	static ILogger getLogger(final String loggerName) {
		throw new UnsupportedOperationException(
				"You should never use the static logger method getLogger(String)! " + loggerName);
	}

	static ILogger getLogger(final Class<?> loggerName) {
		throw new UnsupportedOperationException(
				"You should never use the static logger method getLogger(Class)! " + loggerName);
	}

	static ILogger getRootLogger() {
		throw new UnsupportedOperationException(
				"You should never use the static logger method getRootLogger()osgi.devosgi.devosgi.dev!");
	}

	default void addAppender(final Object something) {
		throw new UnsupportedOperationException("You should never use addAppender on Ultimate loggers!");
	}

	default void removeAppender(final Object mAppender) {
		throw new UnsupportedOperationException("You should never use removeAppender on Ultimate loggers!");
	}

	default Enumeration<?> getAllAppenders() {
		throw new UnsupportedOperationException("You should never use getAllAppenders on Ultimate loggers!");
	}
}
