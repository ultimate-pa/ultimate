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
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.services.model.IResultService;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

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
			String category, String message, String testname, IResultService resultService) {
		Collection<Benchmark> benchmarkSingleton = TestUtil.getCsvProviderProviderFromUltimateResults(resultService.getResults(), Benchmark.class);
		if (benchmarkSingleton.size() != 1) {
			throw new AssertionError("expected single benchmark result");
		} else {
			Benchmark benchmark = benchmarkSingleton.iterator().next();
			double time = benchmark.getElapsedTime(de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.Activator.s_PLUGIN_NAME, TimeUnit.SECONDS);
			m_Results.add(new SummaryEntry(threeValuedResult, message, time, ultimateRunDefinition.getInput()[0]));
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
