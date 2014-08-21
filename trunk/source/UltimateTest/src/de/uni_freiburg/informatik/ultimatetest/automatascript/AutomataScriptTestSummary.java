package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

public class AutomataScriptTestSummary implements ITestSummary {
	
	
	private String m_Name;
	private String m_LogFilePath;
	private ITestResultDecider m_TestResultDecider;
	private List<Triple<String, String, String>> m_Results;

	public AutomataScriptTestSummary(String summaryName, String logFilePath) {
		m_Name = summaryName;
		m_LogFilePath = logFilePath;
		m_Results = new ArrayList<Triple<String, String, String>>();
	}

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		sb.append("################# ");
		sb.append(m_Name);
		sb.append(" #################");
		sb.append("\n");
		for (Triple<String, String, String> triple  : m_Results) {
			sb.append(triple.getFirst());
			sb.append("\t");
			sb.append(triple.getSecond());
			sb.append("\t");
			sb.append(triple.getThird());
			sb.append("\n");
		}
		return sb.toString();
	}

	@Override
	public File getSummaryLogFileName() {
		return new File(m_LogFilePath);
	}

	@Override
	public String getTestSuiteCanonicalName() {
		return m_Name;
	}

	@Override
	public void addResult(TestResult actualResult, boolean junitResult,
			String category, UltimateRunDefinition ultimateRunDefinition, String message) {
		m_Results.add(new Triple<String, String, String>(ultimateRunDefinition.getInput().getAbsolutePath(), category, message));

	}

	@Override
	public void setTestResultDecider(ITestResultDecider decider) {
		m_TestResultDecider = decider;
	}

}
