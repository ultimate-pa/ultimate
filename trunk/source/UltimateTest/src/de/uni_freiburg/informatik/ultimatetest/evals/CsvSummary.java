package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class CsvSummary extends BaseCsvProviderSummary {

	public CsvSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);

	}

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		PartitionedResults results = partitionResults(mResults.entrySet());
		ICsvProvider<String> csvTotal = makePrintCsvProviderFromResults(results.All);
		csvTotal.toCsv(sb, null);
		sb.append(CoreUtil.getPlatformLineSeparator());

		return sb.toString();
	}
}
