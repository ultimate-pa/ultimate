/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE JUnit Helper Library.
 *
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.mocks;

import java.io.Writer;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class LoggingServiceMock implements ILoggingService {

	private final LogLevel mDefaultLevel;

	LoggingServiceMock(final LogLevel defaultLevel) {
		mDefaultLevel = defaultLevel;
	}

	@Override
	public ILogger getLogger(final String pluginId) {
		return new ConsoleLogger(mDefaultLevel);
	}

	@Override
	public ILogger getLogger(final Class<?> clazz) {
		return new ConsoleLogger(mDefaultLevel);
	}

	@Override
	public ILogger getLoggerForExternalTool(final String id) {
		return new ConsoleLogger(mDefaultLevel);
	}

	@Override
	public ILogger getControllerLogger() {
		return new ConsoleLogger(mDefaultLevel);
	}

	@Override
	public Object getBacking(final ILogger logger, final Class<?> backingType) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addWriter(final Writer writer, final String logPattern) {
		// do nothing
	}

	@Override
	public void removeWriter(final Writer writer) {
		// do nothing
	}

	@Override
	public void reloadLoggers() {
		// do nothing
	}

	@Override
	public void setCurrentControllerID(final String name) {
		// do nothing
	}

	@Override
	public void store(final IToolchainStorage storage) {
		// do nothing
	}

	@Override
	public void setLogLevel(final Class<?> clazz, final LogLevel level) {
		// do nothing
	}

	@Override
	public void setLogLevel(final String id, final LogLevel level) {
		// do nothing
	}
}
