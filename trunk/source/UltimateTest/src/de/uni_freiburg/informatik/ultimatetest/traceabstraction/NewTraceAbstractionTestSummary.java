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

public class NewTraceAbstractionTestSummary implements ITestSummary {

	private final Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private final LinkedHashMap<String, List<Summary>> mSummaryMap;

	public NewTraceAbstractionTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		m_UltimateTestSuite = ultimateTestSuite;
		mSummaryMap = new LinkedHashMap<>();
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
		String lineSeparator = System.getProperty("line.separator");
		String indent = "\t";
		for (String filename : mSummaryMap.keySet()) {
			sb.append(filename).append(lineSeparator);
			for (Summary currentSummary : mSummaryMap.get(filename)) {
				sb.append(currentSummary.toLogString(indent, lineSeparator));
			}
			sb.append(lineSeparator);
		}
		return sb.toString();
	}

	@Override
	public void addResult(TestResult threeValuedResult, String category, UltimateRunDefinition ultimateRunDefintion,
			String message, IResultService resultService) {
		Summary sum = new Summary();
		sum.mThreeValuedResult = threeValuedResult;
		sum.mCategory = category;
		sum.mMessage = message;

		sum.mSettingsFile = ultimateRunDefintion.getSettings().getAbsolutePath();
		sum.interpretUltimateResults(resultService);

		addToMap(ultimateRunDefintion.getInput().getAbsolutePath(), sum);
	}

	private void addToMap(String filename, Summary sum) {
		List<Summary> sumList = mSummaryMap.get(filename);
		if (sumList == null) {
			sumList = new ArrayList<>();
			mSummaryMap.put(filename, sumList);
		}
		sumList.add(sum);
	}

	private class Summary {

		public String mSettingsFile;
		public String mMessage;
		public String mCategory;
		public TestResult mThreeValuedResult;
		public List<String> mFlattenedBenchmarkResults;

		public void interpretUltimateResults(IResultService resultService) {

			mFlattenedBenchmarkResults = new ArrayList<>();

			for (IResult result : Util.filterResults(resultService.getResults(), BenchmarkResult.class)) {
				StringBuilder sb = new StringBuilder();
				sb.append(result.getPlugin()).append(": ").append(result.getShortDescription()).append(": ")
						.append(Util.flatten(result.getLongDescription(), " # "));
				mFlattenedBenchmarkResults.add(sb.toString());
			}
		}

		public StringBuilder toLogString(String indent, String lineSeparator) {
			StringBuilder sb = new StringBuilder();

			sb.append(indent).append(mSettingsFile).append(lineSeparator);
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
