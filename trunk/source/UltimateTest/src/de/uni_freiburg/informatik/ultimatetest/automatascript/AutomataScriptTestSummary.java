package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TraceAbstractionTestResultDecider;

public class AutomataScriptTestSummary implements ITestSummary {
	
	
	private String mName;
	private String mLogFilePath;
	private TraceAbstractionTestResultDecider mTestResultDecider;
	private LinkedHashMap<String, String> mSummaryMap;

	public AutomataScriptTestSummary(String summaryName, String logFilePath) {
		mName = summaryName;
		mLogFilePath = logFilePath;
		mSummaryMap = new LinkedHashMap<>();
	}

	@Override
	public String getSummaryLog() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public File getSummaryLogFileName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getTestSuiteCanonicalName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addResult(TestResult actualResult, boolean junitResult,
			String category, String filename, String message) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setTestResultDecider(ITestResultDecider decider) {
		// TODO Auto-generated method stub

	}

}
