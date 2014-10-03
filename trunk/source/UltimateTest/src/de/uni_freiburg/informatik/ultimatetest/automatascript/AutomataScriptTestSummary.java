package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class AutomataScriptTestSummary implements ITestSummary {
	
	
	private Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private List<SummaryEntry> m_Results;

	public AutomataScriptTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		m_UltimateTestSuite = ultimateTestSuite;
		m_Results = new ArrayList<SummaryEntry>();
	}
	
	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return m_UltimateTestSuite;
	}
	
	@Override
	public String getDescriptiveLogName() {
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
		for (SummaryEntry summaryEntry  : m_Results) {
			sb.append(summaryEntry.getTestResult().toString());
			sb.append("\t");
			sb.append(String.format( "%.2f", summaryEntry.getTime()) + "s");
			sb.append("\t");
			sb.append(summaryEntry.getMessage());
			sb.append("\t");
			sb.append(summaryEntry.getAtsFile().getAbsolutePath());
			sb.append("\n");
		}
		return sb.toString();
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult,
			String category, String message, IResultService resultService) {
		Collection<Benchmark> benchmarkSingleton = Util.filterBenchmarks(resultService.getResults(), Benchmark.class);
		if (benchmarkSingleton.size() != 1) {
			throw new AssertionError("expected single benchmark result");
		} else {
			Benchmark benchmark = benchmarkSingleton.iterator().next();
			double time = benchmark.getElapsedTime(de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.Activator.s_PLUGIN_NAME, TimeUnit.SECONDS);
			m_Results.add(new SummaryEntry(threeValuedResult, message, time, ultimateRunDefinition.getInput()));
		}
		

	}
	
	private class SummaryEntry {
		private final TestResult m_TestResult;
		private final String m_Message;
		private final double m_Time;
		private final File m_AtsFile;
		public SummaryEntry(TestResult testResult, String message, double time,
				File atsFile) {
			super();
			m_TestResult = testResult;
			m_Message = message;
			m_Time = time;
			m_AtsFile = atsFile;
		}
		public TestResult getTestResult() {
			return m_TestResult;
		}
		public String getMessage() {
			return m_Message;
		}
		public double getTime() {
			return m_Time;
		}
		public File getAtsFile() {
			return m_AtsFile;
		}
		
		
		
	}



}
