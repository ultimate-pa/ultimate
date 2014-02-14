package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.result.IResult;

public interface ITestSummary {
	public String getSummaryLog();

	public File getSummaryLogFile();
	
	public String getTestSuiteCanonicalName();

	public void addFail(IResult result, String filename, String message);

	public void addUnknown(IResult result, String filename, String message);

	public void addSuccess(IResult result, String filename, String message);
}