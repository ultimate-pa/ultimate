/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.List;

/**
 * Exception that can be thrown if a plugin detects that the timeout is overdue 
 * or a cancellation of the toolchain was requested.
 * 
 * The core will create TimeoutResult if this exception is thrown.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ToolchainCanceledException extends RuntimeException {

	private static final long serialVersionUID = 7090759880566576629L;

	public static final String MESSAGE = "Timeout or Toolchain cancelled by user";
	
	private final List<RunningTaskInfo> mRunningTaskInfos = new ArrayList<>();

	public ToolchainCanceledException(final Class<?> thrower) {
		this(MESSAGE, new RunningTaskInfo(thrower, null));
	}

	public ToolchainCanceledException(final Class<?> thrower, final String runningTaskDescription) {
		this(MESSAGE, new RunningTaskInfo(thrower, runningTaskDescription));
	}
	
	public ToolchainCanceledException(final RunningTaskInfo runningTaskInfo) {
		this(MESSAGE, runningTaskInfo);
	}
	
	public ToolchainCanceledException(final String message, final Class<?> thrower, final String runningTaskDescription) {
		this(message, new RunningTaskInfo(thrower, runningTaskDescription));
	}
	
	public ToolchainCanceledException(final String message, final RunningTaskInfo runningTaskInfo) {
		super(message);
		mRunningTaskInfos.add(runningTaskInfo);
	}
	
	public void addRunningTaskInfo(final RunningTaskInfo runningTaskInfo) {
		mRunningTaskInfos.add(runningTaskInfo);
	}
	
	public String printRunningTaskInfos() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Cancelled");
		
		for (int i = mRunningTaskInfos.size() - 1; i>= 0; i--) {
			final RunningTaskInfo rti = mRunningTaskInfos.get(i);
			if (rti.getTaskDescription() == null) {
				sb.append(" while executing" + rti.getClassOfTaskExecutor().getSimpleName());
			} else {
				sb.append(" while ");
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
