/*
 * Copyright (C) 2014-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.exceptions;

import java.util.EnumSet;
import java.util.Iterator;

/**
 * Exception that can be thrown if a plugin detects that a user-defined limit was reached. Is a
 * {@link ToolchainCanceledException}, but allows delegation of the decision if the whole toolchain should be canceled
 * to someone higher up in the call chain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class TaskCanceledException extends ToolchainCanceledException {

	public enum UserDefinedLimit {
		/**
		 * We give up because the trace histogram has reached a defined limit
		 */
		TRACE_HISTOGRAM,
		/**
		 * We give up because we have spent more time than allowed for this error location
		 */
		TIME_PER_ERROR_LOCATION,
		/**
		 * We give up because we have seen the same path program more than the allowed number of times
		 */
		PATH_PROGRAM_ATTEMPTS,
		/**
		 * We give up because we have reached the limit on CEGAR iteration
		 */
		ITERATIONS
	}

	private static final long serialVersionUID = 7665045856874634524L;
	private final EnumSet<UserDefinedLimit> mLimits;

	public TaskCanceledException(final UserDefinedLimit limit, final Class<?> thrower,
			final String runningTaskDescription) {
		this(EnumSet.of(limit), thrower, runningTaskDescription);
	}

	public TaskCanceledException(final EnumSet<UserDefinedLimit> limits, final Class<?> thrower,
			final String runningTaskDescription) {
		super(humanReadableLimits(limits), thrower, runningTaskDescription);
		mLimits = limits;
	}

	public EnumSet<UserDefinedLimit> getLimits() {
		return mLimits;
	}

	private static String humanReadableLimits(final EnumSet<UserDefinedLimit> limits) {
		final Iterator<UserDefinedLimit> iter = limits.iterator();
		final StringBuilder sb = new StringBuilder();
		sb.append("The user-defined ");
		if (limits.size() == 1) {
			sb.append("limit ");
			sb.append(iter.next().toString());
			sb.append(" has been reached");
		} else {
			sb.append("limits ");
			sb.append(iter.next().toString());
			while (iter.hasNext()) {
				sb.append(" and ");
				sb.append(iter.next().toString());
			}
			sb.append(" have been reached");
		}
		return sb.toString();
	}

}
