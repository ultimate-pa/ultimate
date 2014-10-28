package de.uni_freiburg.informatik.ultimatetest.summary;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

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
	public void addEntryPreStart(UltimateRunDefinition urd) {
		StringBuilder sb = new StringBuilder();
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getCurrentDateTimeAsString());
		sb.append(" Starting test for ");
		sb.append(urd);
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		writeToFile(sb.toString());
	}

	@Override
	public void addEntryPostCompletion(UltimateRunDefinition urd, TestResult result,
			String resultCategory, String resultMessage, IUltimateServiceProvider services) {
		StringBuilder sb = new StringBuilder();
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getCurrentDateTimeAsString());
		sb.append(" Finishing test with ");
		sb.append(result);
		sb.append(" for ");
		sb.append(urd);
		sb.append(": ");
		sb.append(resultCategory);
		sb.append(": ");
		sb.append(resultMessage);
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		writeToFile(sb.toString());
	}

	protected void writeToFile(String logmessage) {
		if (logmessage == null || logmessage.isEmpty()) {
			return;
		}
		if (mLogFile == null) {
			mLogFile = new File(Util.generateAbsolutePathForLogfile(this));
			if (!mLogFile.isDirectory()) {
				mLogFile.getParentFile().mkdirs();
			}
		}

		try {
			FileWriter fw = new FileWriter(mLogFile, true);

			Logger log = Logger.getLogger(getUltimateTestSuiteClass());
			if (log.getAllAppenders().hasMoreElements()) {
				Logger.getLogger(getUltimateTestSuiteClass()).info(
						"Writing " + getDescriptiveLogName() + " for " + getUltimateTestSuiteClass().getCanonicalName()
								+ " to " + mLogFile.getAbsolutePath());
			}
			fw.append(logmessage);
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
