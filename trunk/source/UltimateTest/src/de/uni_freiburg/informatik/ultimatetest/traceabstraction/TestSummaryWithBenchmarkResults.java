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
		writeToFile(runDef.getInput().getAbsolutePath() + de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator());
	}

	@Override
	public void addEntryPostCompletion(UltimateRunDefinition runDef, TestResult result, String resultCategory,
			String resultMessage, IUltimateServiceProvider services) {
		String indent = "\t";
		String lineSeparator = System.getProperty("line.separator");
		Entry sum = null;
		if (services != null) {
			sum = new Entry(result, resultMessage, runDef, services.getResultService());
		} else {
			sum = new Entry(result, resultMessage, runDef, null);
		}

		writeToFile(sum.toLogString(indent, lineSeparator).append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.getPlatformLineSeparator()).toString());
	}

	private class Entry {

		private final TestResult mThreeValuedResult;
		private final String mMessage;
		private final UltimateRunDefinition mUltimateRunDefinition;
		private final List<String> mFlattenedBenchmarkResults;

		public Entry(TestResult threeValuedResult, String message, UltimateRunDefinition ultimateRunDefinition,
				IResultService resultService) {
			super();
			mThreeValuedResult = threeValuedResult;
			mMessage = message;
			mUltimateRunDefinition = ultimateRunDefinition;
			mFlattenedBenchmarkResults = new ArrayList<>();
			if (resultService != null) {
				interpretUltimateResults(resultService);
			}
		}

		private void interpretUltimateResults(IResultService resultService) {

			for (IResult result : de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.filterResults(resultService.getResults(), BenchmarkResult.class)) {
				StringBuilder sb = new StringBuilder();
				sb.append(result.getPlugin()).append(": ").append(result.getShortDescription()).append(": ")
						.append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.flatten(result.getLongDescription(), " # "));
				mFlattenedBenchmarkResults.add(sb.toString());
			}
		}

		public StringBuilder toLogString(String indent, String lineSeparator) {
			StringBuilder sb = new StringBuilder();

			sb.append(indent).append(mUltimateRunDefinition.getSettings()).append(lineSeparator);
			sb.append(indent).append("Test result: ").append(mThreeValuedResult).append(lineSeparator);
			sb.append(indent).append("Message:     ").append(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil.flatten(mMessage, " # ")).append(lineSeparator);
			if (mFlattenedBenchmarkResults.size() > 0) {
				sb.append(indent).append("Benchmarks:").append(lineSeparator);
				for (String s : mFlattenedBenchmarkResults) {
					sb.append(indent).append(indent).append(s).append(lineSeparator);
				}
			}
			return sb;
		}

	}

}
