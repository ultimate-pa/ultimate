package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;

public interface ITestSummary {
	public String getSummaryLog();

	public File getSummaryLogFile();
	
	public String getTestSuiteCanonicalName();

	public void addFail(String category, String filename, String message);

	public void addUnknown(String category, String filename, String message);

	public void addSuccess(String category, String filename, String message);
}