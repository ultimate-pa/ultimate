package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Summary in which the tests are ordered by filenames and for each test the
 * BenchmarkResults are shown.
 * @author heizmann@informatik.uni-freiburg.de and Daniel Dietsch
 *
 */
public class TestSummaryWithBenchmarkResults implements ITestSummary {

	private final Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private final LinkedHashMap<String, List<Entry>> mSummaryMap;

	public TestSummaryWithBenchmarkResults(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		m_UltimateTestSuite = ultimateTestSuite;
		mSummaryMap = new LinkedHashMap<>();
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
		String lineSeparator = System.getProperty("line.separator");
		String indent = "\t";
		for (String filename : mSummaryMap.keySet()) {
			sb.append(filename).append(lineSeparator);
			for (Entry currentSummary : mSummaryMap.get(filename)) {
				sb.append(currentSummary.toLogString(indent, lineSeparator));
			}
			sb.append(lineSeparator);
		}
		return sb.toString();
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefintion, TestResult threeValuedResult, 
			String category,
			String message, IResultService resultService) {
		Entry sum = new Entry(threeValuedResult, message, ultimateRunDefintion, 
				resultService);
		addToMap(ultimateRunDefintion.getInput().getAbsolutePath(), sum);
	}

	private void addToMap(String filename, Entry sum) {
		List<Entry> sumList = mSummaryMap.get(filename);
		if (sumList == null) {
			sumList = new ArrayList<>();
			mSummaryMap.put(filename, sumList);
		}
		sumList.add(sum);
	}

	private class Entry {

		private final TestResult mThreeValuedResult;
		private final String mMessage;
		private final UltimateRunDefinition m_UltimateRunDefinition;
		private final List<String> mFlattenedBenchmarkResults = new ArrayList<>();
		
		public Entry(TestResult threeValuedResult, String message,
				UltimateRunDefinition ultimateRunDefinition, IResultService resultService) {
			super();
			this.mThreeValuedResult = threeValuedResult;
			this.mMessage =message;
			m_UltimateRunDefinition = ultimateRunDefinition;
			interpretUltimateResults(resultService);
		}

		private void interpretUltimateResults(IResultService resultService) {

			for (IResult result : Util.filterResults(resultService.getResults(), BenchmarkResult.class)) {
				StringBuilder sb = new StringBuilder();
				sb.append(result.getPlugin()).append(": ").append(result.getShortDescription()).append(": ")
						.append(Util.flatten(result.getLongDescription(), " # "));
				mFlattenedBenchmarkResults.add(sb.toString());
			}
		}

		public StringBuilder toLogString(String indent, String lineSeparator) {
			StringBuilder sb = new StringBuilder();

			sb.append(indent).append(m_UltimateRunDefinition.getSettings()).append(lineSeparator);
			sb.append(indent).append("Test result: ").append(mThreeValuedResult).append(lineSeparator);
			sb.append(indent).append("Message:     ").append(Util.flatten(mMessage, " # ")).append(lineSeparator);
			sb.append(indent).append("Benchmarks:").append(lineSeparator);
			for (String s : mFlattenedBenchmarkResults) {
				sb.append(indent).append(indent).append(s).append(lineSeparator);
			}
			return sb;
		}

	}


}
