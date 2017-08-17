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

	private static final String FATAL = "[FATAL]: ";
	private static final String ERROR = "[ERROR]: ";
	private static final String WARN = "[WARN]: ";
	private static final String INFO = "[INFO]: ";
	private static final String DEBUG = "[DEBUG]: ";

	@Override
	public boolean isFatalEnabled() {
		return true;
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		System.out.println(FATAL + msg + " " + t);
	}

	@Override
	public void fatal(final Object msg) {
		System.out.println(FATAL + msg);
	}

	@Override
	public boolean isErrorEnabled() {
		return true;
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		System.out.println(ERROR + msg + " " + t);
	}

	@Override
	public void error(final Object msg) {
		System.out.println(ERROR + msg);
	}

	@Override
	public boolean isWarnEnabled() {
		return true;
	}

	@Override
	public void warn(final Object msg) {
		System.out.println(WARN + msg);
	}

	@Override
	public boolean isInfoEnabled() {
		return true;
	}

	@Override
	public void info(final Object msg) {
		System.out.println(INFO + msg);
	}

	@Override
	public boolean isDebugEnabled() {
		return true;
	}

	@Override
	public void debug(final Object msg) {
		System.out.println(DEBUG + msg);
	}
}