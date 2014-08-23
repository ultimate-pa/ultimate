package de.uni_freiburg.informatik.ultimatetest.translation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class TranslationTestSummary extends TestSummary {

	private String mLogFileDirectory;

	public TranslationTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite, String logFileDirectory) {
		super(ultimateTestSuite);
		mLogFileDirectory = logFileDirectory;
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return this.getClass().getSimpleName();
	}
	
	@Override
	public String getFilenameExtension() {
		return ".log";
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
