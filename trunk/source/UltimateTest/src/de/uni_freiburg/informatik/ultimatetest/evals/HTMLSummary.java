package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class HTMLSummary extends BaseCsvProviderSummary {

	public HTMLSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
	}

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		PartitionedResults results = partitionResults(mResults.entrySet());
		String linebreak = CoreUtil.getPlatformLineSeparator();

		sb.append("<html><body>").append(linebreak);
		sb.append("<h1>").append(Util.generateLogfilename(this)).append("</h1>").append(linebreak);

		List<Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>> partitions = new ArrayList<>();
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Success", results.Success));
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Timeout", results.Timeout));
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Error", results.Error));

		ArrayList<ColumnDefinition> prefixedColumnDefinitions = new ArrayList<>();
		prefixedColumnDefinitions.addAll(ColumnDefinitionUtil.getColumnDefinitionForPrefix());
		prefixedColumnDefinitions.addAll(mColumnDefinitions);

		for (Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> entry : partitions) {
			if (entry.getValue().size() == 0) {
				continue;
			}
			sb.append("<h2>").append(entry.getKey()).append("</h2>").append(linebreak);
			ICsvProvider<String> csvTotal = makePrintCsvProviderFromResults(entry.getValue(), mColumnDefinitions);
			csvTotal = ColumnDefinitionUtil.makeHumanReadable(csvTotal, prefixedColumnDefinitions);
			ColumnDefinitionUtil.renameHeadersToLatexTitles(csvTotal, prefixedColumnDefinitions);
			CsvUtils.toHTML(csvTotal, sb, false, null);
			sb.append(CoreUtil.getPlatformLineSeparator());
		}

		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".html";
	}
}
