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

/**
 * Pair that describes a task that is executed by some class. We use objects of this class to describe was the tool was
 * doing while a timeout occurred.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class RunningTaskInfo {

	private final Class<?> mClassOfTaskExecutor;
	private final String mTaskDescription;

	public RunningTaskInfo(final Class<?> clazz, final String taskDescription) {
		mClassOfTaskExecutor = clazz;
		mTaskDescription = taskDescription;
	}

	public Class<?> getClassOfTaskExecutor() {
		return mClassOfTaskExecutor;
	}

	/**
	 * Return optional description of the algorithm/task that. Null if no optional message was provided. The message
	 * should provide some information that can be helpful for finding the reason for the timeout (e.g., algorithm with
	 * exponential space complexity was applied to problem of input size 23).
	 */
	public String getTaskDescription() {
		return mTaskDescription;
	}

}
