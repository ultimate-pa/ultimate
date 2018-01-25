/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.logs.incremental;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;

public class IncrementalLogWithVMParameters extends DefaultIncrementalLogfile {

	private boolean mFirstRun;
	private int mCountTotal;
	private int mCountCurrent;
	private final long mDeadline;

	public IncrementalLogWithVMParameters(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final long deadline) {
		super(ultimateTestSuite);
		mFirstRun = true;
		mCountCurrent = 0;
		mCountTotal = 0;
		mDeadline = deadline;
	}

	public void setCountTotal(final int total) {
		mCountTotal = total;
	}

	@Override
	public void addEntryPreStart(final UltimateRunDefinition urd, final ILogger testlogger) {
		mCountCurrent++;
		final StringBuilder sb = new StringBuilder();
		final String indent = "\t";
		if (mFirstRun) {
			sb.append(CoreUtil.getCurrentDateTimeAsString());
			sb.append(" First run of ");
			sb.append(getDescriptiveLogName());
			sb.append(CoreUtil.getPlatformLineSeparator());
			// add more stats here
			sb.append(indent)
					.append(String.format("Parameters: heapMaxSize=%s assertions=%s",
							CoreUtil.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true),
							VMUtils.areAssertionsEnabled()))
					.append(CoreUtil.getPlatformLineSeparator());
			sb.append(indent).append(String.format("Test Suite Parameters: Timeout=%s s", mDeadline / 1000))
					.append(CoreUtil.getPlatformLineSeparator());
			sb.append(indent).append("Ultimate Git: " + CoreUtil.readGitVersion(getClass().getClassLoader()))
					.append(CoreUtil.getPlatformLineSeparator());
			mFirstRun = false;
		}
		sb.append(CoreUtil.getCurrentDateTimeAsString());
		sb.append(" ### ");
		sb.append(mCountCurrent);
		if (mCountTotal != 0) {
			sb.append("/");
			sb.append(mCountTotal);
		}
		sb.append(" ### Starting test for ");
		sb.append(urd);
		sb.append(CoreUtil.getPlatformLineSeparator());
		writeToFile(sb.toString(), testlogger);
	}

}
