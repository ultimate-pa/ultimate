package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

public class AutomataScriptTestSummary implements ITestSummary {
	
	
	private Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private String m_LogFilePath;
	private List<Triple<String, String, String>> m_Results;

	public AutomataScriptTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite, String logFilePath) {
		m_UltimateTestSuite = ultimateTestSuite;
		m_LogFilePath = logFilePath;
		m_Results = new ArrayList<Triple<String, String, String>>();
	}
	
	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuite() {
		return m_UltimateTestSuite;
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
		StringBuilder sb = new StringBuilder();
		sb.append("################# ");
		sb.append(m_UltimateTestSuite);
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
		return m_UltimateTestSuite.getCanonicalName();
	}

	@Override
	public void addResult(TestResult actualResult, boolean junitResult,
			String category, UltimateRunDefinition ultimateRunDefinition, String message, Map<String, List<IResult>> ultimateIResults) {
		m_Results.add(new Triple<String, String, String>(ultimateRunDefinition.getInput().getAbsolutePath(), category, message));

	}



}
