package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.DefaultIncrementalLogfile;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Incremental log in which for each test the BenchmarkResults are shown.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class TestSummaryWithBenchmarkResults extends DefaultIncrementalLogfile {

	public TestSummaryWithBenchmarkResults(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	@Override
	public void addEntryPreStart(UltimateRunDefinition runDef) {
		writeToFile(runDef.getInput().getAbsolutePath() + Util.getPlatformLineSeparator());
	}

	@Override
	public void addEntryPostCompletion(UltimateRunDefinition runDef, TestResult result, String resultCategory,
			String resultMessage, IUltimateServiceProvider services) {
		String indent = "\t";
		String lineSeparator = System.getProperty("line.separator");
		Entry sum = new Entry(result, resultMessage, runDef, services.getResultService());
		writeToFile(sum.toLogString(indent, lineSeparator).append(Util.getPlatformLineSeparator()).toString());
	}

	private class Entry {

		private final TestResult mThreeValuedResult;
		private final String mMessage;
		private final UltimateRunDefinition m_UltimateRunDefinition;
		private final List<String> mFlattenedBenchmarkResults = new ArrayList<>();

		public Entry(TestResult threeValuedResult, String message, UltimateRunDefinition ultimateRunDefinition,
				IResultService resultService) {
			super();
			this.mThreeValuedResult = threeValuedResult;
			this.mMessage = message;
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
