/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.mocks;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * A very simple implementation of ILogger. All levels are always enabled, it prints error and fatal on stderr and the
 * rest on stdout.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ConsoleLogger implements ILogger {

	private LogLevel mLevel;
	private ILogFunction mFatal;
	private ILogFunction mError;
	private ILogFunction mWarn;
	private ILogFunction mInfo;
	private ILogFunction mDebug;

	public ConsoleLogger() {
		setLevel(LogLevel.DEBUG);
	}

	public ConsoleLogger(final LogLevel level) {
		setLevel(level);
	}

	@Override
	public boolean isFatalEnabled() {
		return isLevelEnabled(LogLevel.FATAL);
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mFatal.log(msg, t);
	}

	@Override
	public void fatal(final Object msg) {
		mFatal.log(msg);
	}

	@Override
	public boolean isErrorEnabled() {
		return isLevelEnabled(LogLevel.ERROR);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mError.log(msg, t);
	}

	@Override
	public void error(final Object msg) {
		mError.log(msg);
	}

	@Override
	public boolean isWarnEnabled() {
		return isLevelEnabled(LogLevel.WARN);
	}

	@Override
	public void warn(final Object msg) {
		mWarn.log(msg);
	}

	@Override
	public boolean isInfoEnabled() {
		return isLevelEnabled(LogLevel.INFO);
	}

	@Override
	public void info(final Object msg) {
		mInfo.log(msg);
	}

	@Override
	public boolean isDebugEnabled() {
		return isLevelEnabled(LogLevel.DEBUG);
	}

	@Override
	public void debug(final Object msg) {
		mDebug.log(msg);
	}

	@Override
	public void setLevel(final LogLevel level) {
		mLevel = level;
		final ILogFunction log = new Log(mLevel);
		final ILogFunction noLog = new NoLog();
		mDebug = noLog;
		mInfo = noLog;
		mWarn = noLog;
		mError = noLog;
		mFatal = noLog;
		// intentional fall-through
		switch (mLevel) {
		case OFF:
			break;
		case DEBUG:
			mDebug = log;
		case INFO:
			mInfo = log;
		case WARN:
			mWarn = log;
		case ERROR:
			mError = log;
		case FATAL:
			mFatal = log;
			break;
		default:
			throw new UnsupportedOperationException("Unknown log level " + level);
		}
	}

	private boolean isLevelEnabled(final LogLevel level) {
		return level.compareTo(mLevel) != -1;
	}

	private static interface ILogFunction {

		void log(final Object msg);

		void log(final Object msg, Throwable t);
	}

	private final class Log implements ILogFunction {

		private static final String FATAL = "[FATAL]: ";
		private static final String ERROR = "[ERROR]: ";
		private static final String WARN = "[WARN]: ";
		private static final String INFO = "[INFO]: ";
		private static final String DEBUG = "[DEBUG]: ";

		private final String mPrefix;

		private Log(final LogLevel level) {
			switch (level) {
			case DEBUG:
				mPrefix = DEBUG;
				break;
			case ERROR:
				mPrefix = ERROR;
				break;
			case FATAL:
				mPrefix = FATAL;
				break;
			case INFO:
				mPrefix = INFO;
				break;
			case WARN:
				mPrefix = WARN;
				break;
			case OFF:
				throw new IllegalArgumentException("Cannot create Log with LogLevel Off");
			default:
				throw new UnsupportedOperationException("Unhandled log level " + level);
			}
		}

		@Override
		public void log(final Object msg) {
			System.out.println(mPrefix + msg);

		}

		@Override
		public void log(final Object msg, final Throwable t) {
			System.out.println(mPrefix + msg + " " + t);
		}
	}

	private static final class NoLog implements ILogFunction {

		@Override
		public void log(final Object msg) {
			// do nothing
		}

		@Override
		public void log(final Object msg, final Throwable t) {
			// do nothing
		}
	}
}