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

package de.uni_freiburg.informatik.ultimate.ultimatetest.logs;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

public class DefaultIncrementalLogfile implements IIncrementalLog {

	private final Class<? extends UltimateTestSuite> mUltimateTestSuite;
	private File mLogFile;

	public DefaultIncrementalLogfile(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		mUltimateTestSuite = ultimateTestSuite;
	}

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return mUltimateTestSuite;
	}

	@Override
	public String getDescriptiveLogName() {
		return getClass().getSimpleName();
	}

	@Override
	public String getFilenameExtension() {
		return "-incremental.log";
	}

	@Override
	public void addEntryPreStart(UltimateRunDefinition urd, ILogger testlogger) {
		final StringBuilder sb = new StringBuilder();
		sb.append(de.uni_freiburg.informatik.ultimate.util.CoreUtil.getCurrentDateTimeAsString());
		sb.append(" Starting test for ");
		sb.append(urd);
		sb.append(de.uni_freiburg.informatik.ultimate.util.CoreUtil.getPlatformLineSeparator());
		writeToFile(sb.toString(), testlogger);
	}

	@Override
	public void addEntryPostCompletion(UltimateRunDefinition urd, TestResult result, String resultCategory,
			String resultMessage, IUltimateServiceProvider services, ILogger testlogger) {
		final StringBuilder sb = new StringBuilder();
		sb.append(de.uni_freiburg.informatik.ultimate.util.CoreUtil.getCurrentDateTimeAsString());
		sb.append(" Finishing test with ");
		sb.append(result);
		sb.append(" for ");
		sb.append(urd);
		sb.append(": ");
		sb.append(resultCategory);
		sb.append(": ");
		sb.append(resultMessage);
		sb.append(de.uni_freiburg.informatik.ultimate.util.CoreUtil.getPlatformLineSeparator());
		writeToFile(sb.toString(), testlogger);
	}

	protected void writeToFile(String logmessage, ILogger log) {
		if (logmessage == null || logmessage.isEmpty()) {
			return;
		}
		if (mLogFile == null) {
			mLogFile = new File(TestUtil.generateAbsolutePathForLogfile(this));
			if (!mLogFile.isDirectory()) {
				mLogFile.getParentFile().mkdirs();
			}
		}

		try {
			final FileWriter fw = new FileWriter(mLogFile, true);
			log.info("Writing " + getDescriptiveLogName() + " for " + getUltimateTestSuiteClass().getCanonicalName()
					+ " to " + mLogFile.getAbsolutePath());
			fw.append(logmessage);
			fw.close();
		} catch (final IOException e) {
			log.fatal("Could not write " + getDescriptiveLogName() + " to file", e);
		}
	}
}
