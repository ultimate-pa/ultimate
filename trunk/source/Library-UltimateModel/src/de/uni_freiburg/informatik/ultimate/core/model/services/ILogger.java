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

package de.uni_freiburg.informatik.ultimate.core.model.services;

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

	default boolean isFatalEnabled() {
		return isLogLevelEnabled(LogLevel.FATAL);
	}

	void fatal(Object msg, Throwable t);

	default void fatal(final Object msg) {
		log(LogLevel.FATAL, msg);
	}

	default void fatal(final String formatString, final Object... formatArgs) {
		log(LogLevel.FATAL, formatString, formatArgs);
	}

	default boolean isErrorEnabled() {
		return isLogLevelEnabled(LogLevel.ERROR);
	}

	void error(Object msg, Throwable t);

	default void error(final Object msg) {
		log(LogLevel.ERROR, msg);
	}

	default void error(final String formatString, final Object... formatArgs) {
		log(LogLevel.ERROR, formatString, formatArgs);
	}

	default boolean isWarnEnabled() {
		return isLogLevelEnabled(LogLevel.WARN);
	}

	default void warn(final Object msg) {
		log(LogLevel.WARN, msg);
	}

	default void warn(final String formatString, final Object... formatArgs) {
		log(LogLevel.WARN, formatString, formatArgs);
	}

	default boolean isInfoEnabled() {
		return isLogLevelEnabled(LogLevel.INFO);
	}

	default void info(final Object msg) {
		log(LogLevel.INFO, msg);
	}

	default void info(final String formatString, final Object... formatArgs) {
		log(LogLevel.INFO, formatString, formatArgs);
	}

	default boolean isDebugEnabled() {
		return isLogLevelEnabled(LogLevel.DEBUG);
	}

	default void debug(final Object msg) {
		log(LogLevel.DEBUG, msg);
	}

	default void debug(final String formatString, final Object... formatArgs) {
		log(LogLevel.DEBUG, formatString, formatArgs);
	}

	boolean isLogLevelEnabled(LogLevel level);

	void log(LogLevel level, String message);

	default void log(final LogLevel level, final Object msg) {
		if (isLogLevelEnabled(level)) {
			log(level, msg.toString());
		}
	}

	default void log(final LogLevel level, final String formatString, final Object... formatArgs) {
		if (isLogLevelEnabled(level)) {
			log(level, String.format(formatString, formatArgs));
		}
	}

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

	/**
	 * @return An ILogger implementation that never logs
	 */
	static ILogger getDummyLogger() {
		return new ILogger() {

			@Override
			public void setLevel(final LogLevel level) {
				// do nothing
			}

			@Override
			public void log(final LogLevel level, final String message) {
				// do nothing
			}

			@Override
			public boolean isLogLevelEnabled(final LogLevel level) {
				return false;
			}

			@Override
			public void fatal(final Object msg, final Throwable t) {
				// do nothing
			}

			@Override
			public void error(final Object msg, final Throwable t) {
				// do nothing
			}
		};
	}
}
