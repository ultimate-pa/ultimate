package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class NewTraceAbstractionTestSummary implements ITestSummary {

	private String mName;
	private String mLogFilePath;
	private TraceAbstractionTestResultDecider mTestResultDecider;
	private LinkedHashMap<String, List<Summary>> mSummaryMap;

	public NewTraceAbstractionTestSummary(String summaryName, String logFilePath) {
		mName = summaryName;
		mLogFilePath = logFilePath;
		mSummaryMap = new LinkedHashMap<>();
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
	public void addResult(TestResult actualResult, boolean junitResult, String category, String filename, String message) {
		Summary sum = new Summary();
		sum.mActualResult = actualResult;
		sum.mJUnitResult = junitResult;
		sum.mCategory = category;
		sum.mMessage = message;

		if (mTestResultDecider != null) {
			sum.mSettingsFile = mTestResultDecider.getSettingsFile().getAbsolutePath();
			sum.interpretUltimateResults(mTestResultDecider.getUltimateResults());
		}

		addToMap(filename, sum);
	}

	private void addToMap(String filename, Summary sum) {
		List<Summary> sumList = mSummaryMap.get(filename);
		if (sumList == null) {
			sumList = new ArrayList<>();
			mSummaryMap.put(filename, sumList);
		}
		sumList.add(sum);
	}

	@Override
	public File getSummaryLogFileName() {
		return new File(mLogFilePath);
	}

	@Override
	public String getTestSuiteCanonicalName() {
		return mName;
	}

	@Override
	public void setTestResultDecider(ITestResultDecider decider) {
		if (decider instanceof TraceAbstractionTestResultDecider) {
			mTestResultDecider = (TraceAbstractionTestResultDecider) decider;
		} else {
			mTestResultDecider = null;
		}
	}

	private class Summary {

		public String mSettingsFile;
		public String mMessage;
		public String mCategory;
		public boolean mJUnitResult;
		public TestResult mActualResult;
		public List<String> mFlattenedBenchmarkResults;

		public void interpretUltimateResults(Collection<IResult> ultimateResults) {
			if (ultimateResults == null) {
				return;
			}

			mFlattenedBenchmarkResults = new ArrayList<>();

			for (IResult result : Util.filterResults(ultimateResults, BenchmarkResult.class)) {
				StringBuilder sb = new StringBuilder();
				sb.append(result.getPlugin()).append(": ").append(result.getShortDescription()).append(": ")
						.append(Util.flatten(result.getLongDescription(), " # "));
				mFlattenedBenchmarkResults.add(sb.toString());

			}
		}

		public StringBuilder toLogString(String indent, String lineSeparator) {
			StringBuilder sb = new StringBuilder();

			sb.append(indent).append(mSettingsFile).append(lineSeparator);
			sb.append(indent).append("Test result: ").append(mActualResult).append(lineSeparator);
			sb.append(indent).append("Message:     ").append(Util.flatten(mMessage, " # ")).append(lineSeparator);
			sb.append(indent).append("Benchmarks:").append(lineSeparator);
			for (String s : mFlattenedBenchmarkResults) {
				sb.append(indent).append(indent).append(s).append(lineSeparator);
			}

			return sb;
		}

	}

}
