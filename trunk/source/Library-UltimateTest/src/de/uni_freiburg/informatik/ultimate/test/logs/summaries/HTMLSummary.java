/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.logs.summaries;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class HTMLSummary extends BaseCsvProviderSummary {

	public HTMLSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			final ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
	}

	@Override
	public String getLog() {
		final StringBuilder sb = new StringBuilder();
		final PartitionedResults results = partitionResults(mResults.entrySet());
		final String linebreak = CoreUtil.getPlatformLineSeparator();

		sb.append("<html><head><style>td { vertical-align:top;}</style></head><body>").append(linebreak);
		sb.append("<h1>").append(TestUtil.generateLogFilename(this)).append("</h1>").append(linebreak);

		final List<Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>> partitions =
				new ArrayList<>();
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Success", results.Success));
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Timeout", results.Timeout));
		partitions.add(new AbstractMap.SimpleEntry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>>(
				"Error", results.Error));

		final ArrayList<ColumnDefinition> prefixedColumnDefinitions = new ArrayList<>();
		prefixedColumnDefinitions.addAll(ColumnDefinitionUtil.getColumnDefinitionForPrefix());
		prefixedColumnDefinitions.addAll(mColumnDefinitions);

		for (final Entry<String, Collection<Entry<UltimateRunDefinition, ExtendedResult>>> entry : partitions) {
			if (entry.getValue().size() == 0) {
				continue;
			}
			sb.append("<h2>").append(entry.getKey()).append("</h2>").append(linebreak);

			// sort by variant
			final List<Entry<UltimateRunDefinition, ExtendedResult>> currentPartition =
					new ArrayList<>(entry.getValue());
			Collections.sort(currentPartition, (o1, o2) -> o1.getKey().compareTo(o2.getKey()));

			ICsvProvider<String> csvTotal = makePrintCsvProviderFromResults(currentPartition, mColumnDefinitions);
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
