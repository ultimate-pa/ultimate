package de.uni_freiburg.informatik.ultimatetest.summary;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Summarizes all benchmarks of a certain class to a CSV.
 * Searches through all IResults and takes only the BenchmarkResults whose
 * benchmarks is an ICsvProvider<Object>> of a specified type.
 * Each row is extends by an entry for the following.
 * <ul> 
 * <li> File
 * <li> Setting
 * <li> Toolchain
 * <li> Expected Result
 * <li> Computed Result
 * </ul>
 * Furthermore the rows of each Benchmark and each test case are concatenated 
 * to a single CSV.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class CsvConcatenator implements ITestSummary {
	
	private final Class<? extends UltimateTestSuite> m_UltimateTestSuite;
	private final Class<? extends ICsvProviderProvider<Object>> m_Benchmark;
	private ICsvProvider<Object> m_CsvProvider;
	
	public CsvConcatenator(
			Class<? extends UltimateTestSuite> ultimateTestSuite,
			Class<? extends ICsvProviderProvider<Object>> benchmark) {
		super();
		m_UltimateTestSuite = ultimateTestSuite;
		m_Benchmark = benchmark;
	}

	@Override
	public String getSummaryLog() {
		return m_CsvProvider.toCsv().toString();
	}

	@Override
	public Class<? extends UltimateTestSuite> getUltimateTestSuite() {
		return m_UltimateTestSuite;
	}

	@Override
	public String getSummaryTypeDescription() {
		return "Summarized " + m_Benchmark.getSimpleName();
	}

	@Override
	public String getFilenameExtension() {
		return ".csv";
	}

	@Override
	public void addResult(TestResult threeValuedResult, String category,
			UltimateRunDefinition ultimateRunDefinition, String message,
			IResultService resultService) {
		
		for (IResult result : Util.filterResults(resultService.getResults(), BenchmarkResult.class)) {
			BenchmarkResult<Object> benchmarkResult = (BenchmarkResult<Object>) result;
			ICsvProviderProvider<Object> benchmark = benchmarkResult.getBenchmark();
			if (m_Benchmark.isAssignableFrom(benchmark.getClass())) {
				ICsvProvider<Object> benchmarkCsv = (ICsvProvider<Object>) benchmark.createCvsProvider();
				ICsvProvider<Object> benchmarkCsvWithRunDefinition = addUltimateRunDefinition(ultimateRunDefinition,
						benchmarkCsv, category, message);
				add(benchmarkCsvWithRunDefinition);
			}
		}
	}
	
	private void add(ICsvProvider<Object> benchmarkCsvWithRunDefinition) {
		if (m_CsvProvider == null) {
			m_CsvProvider = benchmarkCsvWithRunDefinition;
		} else {
			m_CsvProvider = CsvUtils.concatenateRows(m_CsvProvider,
					benchmarkCsvWithRunDefinition);
		}
		
	}

	private ICsvProvider<Object> addUltimateRunDefinition(
			UltimateRunDefinition ultimateRunDefinition,
			ICsvProvider<Object> benchmark, String category, String message) {
		List<String> resultColumns = new ArrayList<>();
		resultColumns.add("File");
		resultColumns.add("Settings");
		resultColumns.add("Toolchain");
		resultColumns.add("Expected Result");
		resultColumns.add("Message Result");
		resultColumns.addAll(benchmark.getColumnTitles());
		ICsvProvider<Object> result = new SimpleCsvProvider<>(resultColumns);
		int rows = benchmark.getRowHeaders().size();
		for (int i=0; i<rows; i++) {
			List<Object> resultRow = new ArrayList<>();
			resultRow.add(ultimateRunDefinition.getInput().getAbsolutePath());
			resultRow.add(ultimateRunDefinition.getSettings().getAbsolutePath());
			resultRow.add(ultimateRunDefinition.getToolchain().getAbsolutePath());
			resultRow.add(category);
			resultRow.add(message);
			resultRow.addAll(benchmark.getRow(i));
			result.addRow(resultRow);
		}
		return result;
	}

}
