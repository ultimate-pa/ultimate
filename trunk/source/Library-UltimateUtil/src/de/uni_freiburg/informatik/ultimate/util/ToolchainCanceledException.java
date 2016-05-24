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

/**
 * Exception that can be thrown if a plugin detects that the timeout is overdue or a cancellation of the toolchain was
 * requested.
 * 
 * The core will create TimeoutResult if this exception is thrown.
 *
 * @author heizmann
 */
public class ToolchainCanceledException extends RuntimeException {

	private static final long serialVersionUID = 7090759880566576629L;

	public static final String MESSAGE = "Timeout or Toolchain cancelled by user";
	private final Class<?> mClassOfThrower;
	private final String mRunningTaskInfo;

	public ToolchainCanceledException(Class<?> thrower) {
		super(MESSAGE);
		mClassOfThrower = thrower;
		mRunningTaskInfo = null;
	}

	public ToolchainCanceledException(Class<?> thrower, String runningTaskInfo) {
		super(MESSAGE);
		mClassOfThrower = thrower;
		mRunningTaskInfo = runningTaskInfo;
	}

	@Override
	public String getMessage() {
		return super.getMessage();
	}

	/**
	 * Get the class of the object that has thrown this Exception.
	 * 
	 * @return
	 */
	public Class<?> getClassOfThrower() {
		return mClassOfThrower;
	}

	/**
	 * Return optional message that was added by the algorithm/task that has thrown this Exception. Null if no optional
	 * message was provided. The message should provide some information that can be helpful for finding the reason for
	 * the timeout (e.g., algorithm with exponential space complexity was applied to problem of input size 23).
	 */
	public String getRunningTaskInfo() {
		return mRunningTaskInfo;
	}

	public String prettyPrint() {
		return "(Timeout occurred in class " + getClassOfThrower().getSimpleName()
				+ (getRunningTaskInfo() == null ? "" : " during the following task: " + getRunningTaskInfo())
				+ ")";
	}

}
