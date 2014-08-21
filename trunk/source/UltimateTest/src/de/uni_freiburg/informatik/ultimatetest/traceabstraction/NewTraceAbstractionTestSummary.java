package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class NewTraceAbstractionTestSummary implements ITestSummary {

	private final String mName;
	private final String mLogFilePath;
	private final String m_TestDescription;
	private TraceAbstractionTestResultDecider mTestResultDecider;
	private final LinkedHashMap<String, List<Summary>> mSummaryMap;
	private CsvProviderSummary m_CsvProviderSummary = new CsvProviderSummary();

	public NewTraceAbstractionTestSummary(String summaryName, String description) {
		mName = summaryName;
		m_TestDescription = description;
		mLogFilePath = Util.generateSummaryLogFilename(
				Util.getPathFromSurefire(".", this.getClass().getCanonicalName()), description);
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
//		Hack for checking if csv output is working		
//		m_CsvProviderSummary.writeAllCsv();
		return sb.toString();
	}

	@Override
	public void addResult(TestResult actualResult, boolean junitResult, String category, 
			UltimateRunDefinition ultimateRunDefintion, String message) {
		Summary sum = new Summary();
		sum.mActualResult = actualResult;
		sum.mJUnitResult = junitResult;
		sum.mCategory = category;
		sum.mMessage = message;

		if (mTestResultDecider != null) {
			sum.mSettingsFile = mTestResultDecider.getSettingsFile().getAbsolutePath();
			sum.interpretUltimateResults(mTestResultDecider.getUltimateResults());
		}
		
		for (IResult result : Util.filterResults(mTestResultDecider.getUltimateResults(), BenchmarkResult.class)) {
			m_CsvProviderSummary.add(ultimateRunDefintion, (BenchmarkResult<?>) result);
		}

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
	
	public void writeAllCsv() {
		
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
	
	private class CsvProviderSummary {
		private Map<Class, ICsvProvider> m_Benchmark2CsvProvider = new HashMap<Class, ICsvProvider>();
		
		void add(UltimateRunDefinition ultimateRunDefintion, BenchmarkResult<?> result) {
			ICsvProviderProvider<?> benchmark = result.getBenchmark();
			ICsvProvider<?> benchmarkCsv = benchmark.createCvsProvider();
			ICsvProvider oldCsvProvider = m_Benchmark2CsvProvider.get(benchmark.getClass());
			if (oldCsvProvider == null) {
				oldCsvProvider = new SimpleCsvProvider<>(benchmarkCsv.getColumnTitles());
				m_Benchmark2CsvProvider.put(benchmark.getClass(), oldCsvProvider);
			}
			if (benchmarkCsv.getRowTitles().length != 1) {
				throw new AssertionError("expecting that benchmark has exactly one row");
			}
			ICsvProvider benchmarkCsvWithDescription  = new SimpleCsvProvider<>(benchmarkCsv.getColumnTitles());
			benchmarkCsvWithDescription.addRow(ultimateRunDefintion.toString(), benchmarkCsv.getRow(benchmark.getClass().getName()));
//			for (String test : benchmarkCsv.getRowTitles()) {
//				
//			}
			ICsvProvider newCsvProvider = CsvUtils.concatenateRowsWithDifferentColumns(oldCsvProvider, benchmarkCsv);
			m_Benchmark2CsvProvider.put(benchmark.getClass(), newCsvProvider);

		}
		
		
		private void writeAllCsv() {
			
			for (Entry<Class, ICsvProvider> entry : m_Benchmark2CsvProvider.entrySet()) {
				String csvFileName = entry.getKey().getName() + getTestSuiteCanonicalName();
				File csvFile = new File(Util.getPathFromSurefire("test.csv", getTestSuiteCanonicalName()));
				
				try {
					FileWriter fw = new FileWriter(csvFile);
					Logger.getLogger(UltimateTestSuite.class).info(
							"Writing CSV for " + entry.getKey() + " to " + csvFile.getAbsolutePath());
					fw.write(entry.getValue().toString());
					fw.close();
				} catch (IOException e) {
					e.printStackTrace();
				}

			}
			

//			File logFile = new File(Util.getPathFromSurefire(mLogFilePath, getTestSuiteCanonicalName()));
//
//			if (!logFile.isDirectory()) {
//				logFile.getParentFile().mkdirs();
//			}

//			String summaryLog = summary.getSummaryLog();
//			if (summaryLog == null || summaryLog.isEmpty()) {
//				return;
//			}

		}

		

	}
	
	
	

}
