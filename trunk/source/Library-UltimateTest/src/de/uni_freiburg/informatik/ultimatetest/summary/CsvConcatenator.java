package de.uni_freiburg.informatik.ultimatetest.summary;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Summarizes all benchmarks of a certain class to a CSV. Searches through all
 * IResults and takes only the BenchmarkResults whose benchmarks is an
 * ICsvProvider<Object>> of a specified type. Each row is extends by an entry
 * for the following.
 * <ul>
 * <li>File
 * <li>Setting
 * <li>Toolchain
 * </ul>
 * Furthermore the rows of each Benchmark and each test case are concatenated to
 * a single CSV.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class CsvConcatenator implements ITestSummary {

	private final Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private final Class<? extends ICsvProviderProvider<Object>> m_Benchmark;
	private ICsvProvider<Object> m_CsvProvider;

	public CsvConcatenator(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Class<? extends ICsvProviderProvider<Object>> benchmark) {
		super();
		m_UltimateTestSuite = ultimateTestSuite;
		m_Benchmark = benchmark;
		List<String> emtpyList = Collections.emptyList();
		m_CsvProvider = new SimpleCsvProvider<Object>(emtpyList);
	}

	@Override
	public String getSummaryLog() {
		return m_CsvProvider.toCsv().toString();
	}

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuiteClass() {
		return m_UltimateTestSuite;
	}

	@Override
	public String getDescriptiveLogName() {
		return "Summarized " + m_Benchmark.getSimpleName();
	}

	@Override
	public String getFilenameExtension() {
		return ".csv";
	}

	@Override
	public void addResult(UltimateRunDefinition ultimateRunDefinition, TestResult threeValuedResult, String category,
			String message, String testname, IResultService resultService) {
		if (resultService == null) {
			return;
		}
		for (ICsvProviderProvider<Object> benchmarkResult : Util.filterBenchmarks(resultService.getResults(),
				m_Benchmark)) {
			ICsvProvider<Object> benchmarkCsv = benchmarkResult.createCvsProvider();
			ICsvProvider<Object> benchmarkCsvWithRunDefinition = addUltimateRunDefinition(ultimateRunDefinition,
					benchmarkCsv, category, message);
			add(benchmarkCsvWithRunDefinition);
		}
	}

	private void add(ICsvProvider<Object> benchmarkCsvWithRunDefinition) {
		m_CsvProvider = CsvUtils.concatenateRows(m_CsvProvider, benchmarkCsvWithRunDefinition);
	}

	private ICsvProvider<Object> addUltimateRunDefinition(UltimateRunDefinition ultimateRunDefinition,
			ICsvProvider<Object> benchmark, String category, String message) {
		List<String> resultColumns = new ArrayList<>();
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.addAll(benchmark.getColumnTitles());
		ICsvProvider<Object> result = new SimpleCsvProvider<>(resultColumns);
		int rows = benchmark.getRowHeaders().size();
		for (int i = 0; i < rows; i++) {
			List<Object> resultRow = new ArrayList<>();
			resultRow.add(ultimateRunDefinition.getInput().getAbsolutePath());
			resultRow.add(ultimateRunDefinition.getSettings().getAbsolutePath());
			resultRow.add(ultimateRunDefinition.getToolchain().getAbsolutePath());
			resultRow.addAll(benchmark.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

}
