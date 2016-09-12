/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;

/**
 * IResult that is reported if toolchain has thrown a Throwable (Error or Exception). The Throwable stored in the result
 * has to be the Throwable that was thrown by the toolchain.
 *
 * @author Matthias Heizmann
 */
public class ExceptionOrErrorResult extends AbstractResult {
	private final Throwable mThrowable;

	public ExceptionOrErrorResult(final String plugin, final Throwable throwable) {
		super(getPluginName(plugin, throwable));
		if (throwable instanceof ToolchainExceptionWrapper) {
			mThrowable = ((ToolchainExceptionWrapper) throwable).getCause();
		} else {
			mThrowable = throwable;
		}
	}

	private static String getPluginName(final String plugin, final Throwable throwable) {
		if (throwable instanceof ToolchainExceptionWrapper) {
			return ((ToolchainExceptionWrapper) throwable).getPluginId();
		} else {
			return plugin;
		}
	}

	@Override
	public String getShortDescription() {
		return mThrowable.getClass().getSimpleName() + ": " + mThrowable.getMessage();
	}

	@Override
	public String getLongDescription() {
		final StackTraceElement[] stacktrace = mThrowable.getStackTrace();
		String rtr = getPlugin() + ": " + getShortDescription();
		if (stacktrace != null && stacktrace.length > 0) {
			rtr = rtr + ": " + stacktrace[0].toString();
		}
		return rtr;
	}

	@Override
	public String toString() {
		return getLongDescription();
	}
}
