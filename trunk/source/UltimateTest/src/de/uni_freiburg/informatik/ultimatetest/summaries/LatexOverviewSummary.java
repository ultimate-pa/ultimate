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
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class LatexOverviewSummary extends LatexSummary {

	private static final String NO_SETTINGS_NAME = "No settings";
	private final int mLatexTableHeaderCount;

	/**
	 * Create a summary that prints a file containing LaTex table for each toolchain. The table groups test runs by
	 * folder name and compares them against different setting files.
	 *
	 * The values result from benchmark providers collected during the Ultimate runs.
	 *
	 * @param ultimateTestSuite
	 *            To which testsuite belongs this summary?
	 * @param benchmarks
	 *            A list of benchmark types that should be included in the table.
	 * @param columnDefinitions
	 *            An array of column definitions that specify how the benchmark results should be processed (values as
	 *            well as strings)
	 */
	public LatexOverviewSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			final ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
		mLatexTableHeaderCount = (int) mColumnDefinitions.stream().filter(a -> a.getLatexColumnTitle() != null).count();
	}

	@Override
	public String getSummaryLog() {
		final StringBuilder sb = new StringBuilder();
		final PartitionedResults results = partitionResults(mResults.entrySet());
		makeTables(sb, results);
		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}

	private void makeTables(final StringBuilder sb, final PartitionedResults results) {
		final Set<String> tools =
				results.All.stream().map(a -> a.getKey().getToolchain().getName()).collect(Collectors.toSet());
		final String br = CoreUtil.getPlatformLineSeparator();

		appendPreamble(sb, br);

		for (final String tool : tools) {
			// make table header
			sb.append("\\begin{longtabu} to \\linewidth {lcllc");
			for (int i = 0; i < mLatexTableHeaderCount; ++i) {
				sb.append("r");
			}
			sb.append("}").append(br);
			sb.append("\\toprule").append(br);
			sb.append("  \\header{}& ").append(br);
			sb.append("  \\header{\\#}&").append(br);
			sb.append("  \\header{Result}&").append(br);
			sb.append("  \\header{Variant}& ").append(br);
			sb.append("  \\header{Count}&").append(br);

			int i = 0;
			for (final ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getLatexColumnTitle() == null) {
					continue;
				}
				sb.append("  \\header{");
				sb.append(removeInvalidCharsForLatex(cd.getLatexColumnTitle()));
				sb.append("}");
				i++;
				if (i < mLatexTableHeaderCount) {
					sb.append("&");
				} else {
					sb.append("\\\\");
				}
				sb.append(br);
			}
			sb.append("  \\cmidrule(r){2-");
			sb.append(5 + mLatexTableHeaderCount);
			sb.append("}").append(br);

			// make table body

			final PartitionedResults resultsPerTool = partitionResults(results.All.stream()
					.filter(a -> a.getKey().getToolchain().getName().equals(tool)).collect(Collectors.toList()));
			makeTableBody(sb, resultsPerTool, tool);

			// end table
			sb.append("\\caption{Results for ").append(removeInvalidCharsForLatex(tool)).append(".}").append(br);
			sb.append("\\end{longtabu}").append(br);
		}

		// append finishing code
		appendEnd(sb, br);
	}

	private void appendEnd(final StringBuilder sb, final String br) {
		sb.append("\\end{document}").append(br);
	}

	private void appendPreamble(final StringBuilder sb, final String br) {
		// append preamble
		sb.append("\\documentclass[a3paper]{article}").append(br);
		sb.append("\\usepackage[a3paper, margin=1.5cm, top=1.1cm]{geometry}").append(br);
		sb.append("\\usepackage[table]{xcolor} ").append(br);
		sb.append("\\usepackage[utf8]{inputenc}").append(br);
		sb.append("\\usepackage{amsmath,amssymb}").append(br);
		sb.append("\\usepackage{booktabs}").append(br);
		sb.append("\\usepackage{tabu}").append(br);
		sb.append("\\usepackage{multirow}").append(br);
		sb.append("\\usepackage{url}").append(br);
		sb.append("\\usepackage{xspace}").append(br);
		sb.append("\\usepackage{graphicx}").append(br);
		sb.append("\\usepackage{longtable}").append(br);
		sb.append("").append(br);
		sb.append("\\begin{document}").append(br);

		// append commands
		sb.append("\\newcommand{\\headcolor}{}").append(br);
		sb.append("\\newcommand{\\header}[1]{\\parbox{2.8em}{\\centering #1}\\headcolor}").append(br);
		sb.append("\\newcommand{\\folder}[1]{\\parbox{5em}{#1}}").append(br);
	}

	private void makeTableBody(final StringBuilder sb, final PartitionedResults results, final String toolname) {
		// make header
		final Set<String> distinctSuffixes = getDistinctFolderSuffixes(results);

		int i = 0;
		for (final String suffix : distinctSuffixes) {
			final PartitionedResults resultsPerFolder =
					partitionResults(
							results.All.stream()
									.filter(entry -> Arrays.stream(entry.getKey().getInput())
											.anyMatch(a -> a.getParent().endsWith(suffix)))
									.collect(Collectors.toList()));
			i++;
			makeFolderRow(sb, resultsPerFolder, suffix, i >= distinctSuffixes.size());
		}
	}

	private void makeFolderRow(final StringBuilder sb, final PartitionedResults results, final String folder,
			final boolean last) {
		final String br = CoreUtil.getPlatformLineSeparator();
		final int resultRows = 4;
		final List<String> variants =
				results.All.stream().map(a -> a.getKey().getSettingsName()).distinct().collect(Collectors.toList());

		// folder name
		sb.append("\\multirow{");
		sb.append(variants.size() * resultRows);
		sb.append("}{*}{\\folder{");
		sb.append(removeInvalidCharsForLatex(folder));
		sb.append("}} &").append(br);

		// count expected unsafe & row header unsafe
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.ExpectedUnsafe / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Unsafe}} ").append(br);

		// results unsafe
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Unsafe, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// count expected safe & row header safe
		sb.append("& \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.ExpectedSafe / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Safe}} ").append(br);

		// results safe
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Safe, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// count total & row header total
		sb.append("& \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{");
		sb.append(results.All.size() / variants.size());
		sb.append("} &").append(br);
		sb.append("\\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Completed}} ").append(br);
		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> completed = new ArrayList<>();
		completed.addAll(results.Safe);
		completed.addAll(results.Unsafe);
		for (int i = 0; i < variants.size(); ++i) {
			// this is the last in the foldoer row, so it gets a different
			// separator, hence false == isLast
			makeVariantEntry(sb, completed, variants.get(i), i == 0);
		}
		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + 5);
		sb.append("}").append(br);

		// row timeout
		sb.append("& & \\multirow{");
		sb.append(variants.size());
		sb.append("}{*}{\\folder{Timeout}} ").append(br);
		for (int i = 0; i < variants.size(); ++i) {
			makeVariantEntry(sb, results.Timeout, variants.get(i), i == 0);
		}

		if (last) {
			sb.append("\\bottomrule").append(br);
			for (int i = 0; i < mLatexTableHeaderCount + 4; ++i) {
				sb.append("& ");
			}
			sb.append("\\\\").append(br);
		} else {
			sb.append("\\midrule").append(br);
		}
	}

	private void makeVariantEntry(final StringBuilder sb,
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> current, final String variant,
			final boolean isFirst) {

		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> results =
				current.stream().filter(a -> a.getKey().getSettingsName().equals(variant)).collect(Collectors.toList());

		final String br = CoreUtil.getPlatformLineSeparator();
		final String sep = " & ";

		if (isFirst) {
			sb.append(sep);
		} else {
			sb.append(sep).append(sep).append(sep);
		}
		sb.append(removeInvalidCharsForLatex(variant));
		sb.append(sep);

		ICsvProvider<String> csv = makePrintCsvProviderFromResults(results, mColumnDefinitions);

		csv = CsvUtils.projectColumn(csv,
				mColumnDefinitions.stream().map(a -> a.getCsvColumnTitle()).collect(Collectors.toList()));

		csv = ColumnDefinitionUtil.reduceProvider(csv,
				mColumnDefinitions.stream().map(a -> a.getManyRunsToOneRow()).collect(Collectors.toList()),
				mColumnDefinitions);

		csv = ColumnDefinitionUtil.makeHumanReadable(csv, mColumnDefinitions);
		csv = CsvUtils.addColumn(csv, "Count", 0, Arrays.asList(new String[] { Integer.toString(results.size()) }));

		// make list of indices to ignore idx -> true / false
		final boolean[] idx = new boolean[csv.getColumnTitles().size()];
		// because of count
		idx[0] = true;
		for (int i = 1; i < idx.length; ++i) {
			final String currentHeader = csv.getColumnTitles().get(i);
			for (final ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getCsvColumnTitle().equals(currentHeader)) {
					idx[i] = (cd.getLatexColumnTitle() != null);
					break;
				}
			}
		}

		// one more because of Count
		final int length = mLatexTableHeaderCount + 1;
		int i = 0;
		final List<String> row = csv.getRow(0);
		if (row == null || row.isEmpty()) {
			// no results in this category, just fill with empty fields
			for (; i < length; ++i) {
				sb.append(sep);
			}
		} else {
			for (final String cell : row) {
				if (!idx[i]) {
					// skip this column, we dont want to print it
					i++;
					continue;
				}
				if (isInvalidForLatex(cell)) {
					sb.append("-I-");
				} else {
					sb.append(removeInvalidCharsForLatex(cell));
				}

				if (i < row.size() - 1) {
					sb.append(sep);
				}
				i++;
			}
		}
		sb.append("\\\\");
		sb.append(br);
	}
}
