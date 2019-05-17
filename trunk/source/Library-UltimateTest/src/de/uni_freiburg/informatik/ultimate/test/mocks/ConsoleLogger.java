/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2015,2019 University of Freiburg
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
	private ILogFunction[] mLevelToFunction = new ILogFunction[LogLevel.values().length];

	public ConsoleLogger() {
		setLevel(LogLevel.DEBUG);
	}

	public ConsoleLogger(final LogLevel level) {
		setLevel(level);
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLevelToFunction[LogLevel.FATAL.ordinal()].log(msg, t);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLevelToFunction[LogLevel.ERROR.ordinal()].log(msg, t);
	}

	@Override
	public void log(final LogLevel level, final String msg) {
		mLevelToFunction[level.ordinal()].log(msg);
	}

	@Override
	public void setLevel(final LogLevel level) {
		mLevel = level;
		final ILogFunction noLog = new NoLog();
		for (LogLevel levelIter : LogLevel.values()) {
			mLevelToFunction[levelIter.ordinal()] = isLogLevelEnabled(levelIter) ?
					new Log("[" + levelIter + "]: ") : noLog;
		}
	}

	@Override
	public boolean isLogLevelEnabled(final LogLevel queryLevel) {
		// lower levels log more, see documentation of ILogger.LogLevel
		return queryLevel.compareTo(mLevel) >= 0;
	}

	private static interface ILogFunction {

		void log(final Object msg);

		void log(final Object msg, Throwable t);
	}

	private static final class Log implements ILogFunction {

		private final String mPrefix;

		private Log(final String prefix) {
			mPrefix = prefix;
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