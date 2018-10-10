/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.List;

/**
 * {@link IRunningTaskStackProvider} describes a stack of operations that were executed and which lead to an exception.
 * This interface is used in conjunction with certain exceptions (e.g., {@link ToolchainCanceledException}) to generate
 * more informative error messages.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public interface IRunningTaskStackProvider {

	/**
	 * Get a {@link List} of {@link RunningTaskInfo} instances that describe what happened up until now.
	 */
	List<RunningTaskInfo> getRunningTaskStack();

	/**
	 * Convert the current RunningTaskStack obtained with {@link #getRunningTaskStack()} to a human-readable error
	 * message.
	 */
	default public String printRunningTaskMessage() {
		final StringBuilder sb = new StringBuilder();

		final List<RunningTaskInfo> runningTaskStack = getRunningTaskStack();
		for (int i = runningTaskStack.size() - 1; i >= 0; i--) {
			final RunningTaskInfo rti = runningTaskStack.get(i);
			if (rti.getTaskDescription() == null) {
				sb.append("while executing " + rti.getClassOfTaskExecutor().getSimpleName());
			} else {
				sb.append("while ");
				sb.append(rti.getClassOfTaskExecutor().getSimpleName());
				sb.append(" was ");
				sb.append(rti.getTaskDescription());
			}
			if (i > 0) {
				sb.append(",");
			}
		}
		sb.append(".");
		return sb.toString();
	}

}