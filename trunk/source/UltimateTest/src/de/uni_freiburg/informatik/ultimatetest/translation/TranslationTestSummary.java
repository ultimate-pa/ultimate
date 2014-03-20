package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class TranslationTestSummary extends TestSummary {

	private String mLogFileDirectory;

	public TranslationTestSummary(String testSuiteCanonicalName, String logFileDirectory) {
		super(testSuiteCanonicalName);
		mLogFileDirectory = logFileDirectory;
	}

	@Override
	public String getSummaryLog() {
		return generateCanonicalSummary().toString();
	}

	@Override
	public File getSummaryLogFileName() {
		return new File(Util.generateSummaryLogFilename(mLogFileDirectory, getTestSuiteCanonicalName()));
	}

}
