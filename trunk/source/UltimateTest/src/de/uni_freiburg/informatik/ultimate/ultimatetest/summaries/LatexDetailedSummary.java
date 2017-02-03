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
package de.uni_freiburg.informatik.ultimate.ultimatetest.summaries;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class LatexDetailedSummary extends LatexSummary {

	private final int mLatexTableHeaderCount;

	public LatexDetailedSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			final ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);

		mLatexTableHeaderCount =
				CoreUtil.reduce(mColumnDefinitions, new CoreUtil.IMapReduce<Integer, ColumnDefinition>() {
					@Override
					public Integer reduce(Integer lastValue, final ColumnDefinition entry) {
						if (lastValue == null) {
							lastValue = 0;
						}
						return entry.getLatexColumnTitle() != null ? lastValue + 1 : lastValue;
					}
				});
	}

	@Override
	public String getSummaryLog() {
		final StringBuilder sb = new StringBuilder();
		final PartitionedResults results = partitionResults(mResults.entrySet());

		try {
			makeTables(sb, results);
		} catch (final Error e) {
			return "";
		}

		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}

	private void makeTables(final StringBuilder sb, final PartitionedResults results) {

		final int additionalHeaders = 4;

		final Set<String> tools = CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getToolchain().getName();
			}
		});

		final String br = CoreUtil.getPlatformLineSeparator();

		appendPreamble(sb, br);

		for (final String tool : tools) {
			// make table header
			sb.append("\\begin{longtabu} to \\linewidth {llll");
			for (int i = 0; i < mLatexTableHeaderCount; ++i) {
				sb.append("r");
			}
			sb.append("}").append(br);
			sb.append("\\toprule").append(br);
			sb.append("  \\header{}& ").append(br);
			sb.append("  \\header{Result}&").append(br);
			sb.append("  \\header{File}& ").append(br);
			sb.append("  \\header{Variant}& ").append(br);

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
			sb.append(additionalHeaders + mLatexTableHeaderCount);
			sb.append("}").append(br);

			// make table body
			final PartitionedResults resultsPerTool =
					partitionResults(CoreUtil.where(results.All, new ITestSummaryResultPredicate() {
						@Override
						public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().getName().equals(tool);
						}
					}));
			makeTableBody(sb, resultsPerTool, tool, additionalHeaders);

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
		sb.append("\\documentclass[a3paper,landscape]{article}").append(br);
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

	private void makeTableBody(final StringBuilder sb, final PartitionedResults results, final String toolname,
			final int additionalTableHeaders) {
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
			makeFolderRow(sb, resultsPerFolder, suffix, i >= distinctSuffixes.size(), additionalTableHeaders);
		}
	}

	private void makeFolderRow(final StringBuilder sb, final PartitionedResults results, final String folder,
			final boolean last, final int additionalTableHeaders) {
		final String br = CoreUtil.getPlatformLineSeparator();
		final int additionalHeaders = additionalTableHeaders;

		final List<String> files = new ArrayList<>(CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getInputFileNames();
			}
		}));

		final int safeRows = (results.Safe.size() == 0 ? 1 : results.Safe.size());
		final int unsafeRows = (results.Unsafe.size() == 0 ? 1 : results.Unsafe.size());
		final int timeoutRows = (results.Timeout.size() == 0 ? 1 : results.Timeout.size());
		final int errorRows = (results.Error.size() == 0 ? 1 : results.Error.size());
		final int folderRows = safeRows + unsafeRows + timeoutRows + errorRows;

		// folder name header
		sb.append("\\multirow{");
		sb.append(folderRows);
		sb.append("}{*}{\\folder{");
		sb.append(removeInvalidCharsForLatex(folder));
		sb.append("}}").append(br);

		// row header unsafe
		sb.append("& \\multirow{");
		sb.append(unsafeRows);
		sb.append("}{*}{");
		sb.append("\\folder{Unsafe}} ").append(br);

		// results unsafe
		makeFileEntry(sb, results.Unsafe, files);

		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + additionalHeaders);
		sb.append("}").append(br);

		// row header safe
		sb.append("& \\multirow{");
		sb.append(safeRows);
		sb.append("}{*}{");
		sb.append("\\folder{Safe}} ").append(br);

		// results safe
		makeFileEntry(sb, results.Safe, files);

		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + additionalHeaders);
		sb.append("}").append(br);

		// row header timeout
		sb.append("& \\multirow{");
		sb.append(timeoutRows);
		sb.append("}{*}{\\folder{Timeout}} ").append(br);

		// results timeout
		makeFileEntry(sb, results.Timeout, files);

		sb.append("  \\cmidrule[0.01em](l){2-");
		sb.append(mLatexTableHeaderCount + additionalHeaders);
		sb.append("}").append(br);

		// row header error
		sb.append("& \\multirow{");
		sb.append(errorRows);
		sb.append("}{*}{\\folder{Error}} ").append(br);

		// results error
		makeFileEntry(sb, results.Error, files);

		// table body ending
		if (last) {
			sb.append("\\bottomrule").append(br);
			for (int i = 0; i < mLatexTableHeaderCount + additionalHeaders - 1; ++i) {
				sb.append("& ");
			}
			sb.append("\\\\").append(br);
		} else {
			sb.append("\\midrule").append(br);
		}
	}

	private void makeFileEntry(final StringBuilder sb,
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> current, final List<String> files) {

		final List<Entry<UltimateRunDefinition, ExtendedResult>> results = current.stream()
				.filter(a -> files.contains(a.getKey().getInputFileNames())).collect(Collectors.toList());

		Collections.sort(results, new Comparator<Entry<UltimateRunDefinition, ExtendedResult>>() {
			@Override
			public int compare(final Entry<UltimateRunDefinition, ExtendedResult> o1,
					final Entry<UltimateRunDefinition, ExtendedResult> o2) {
				return o1.getKey().compareTo(o2.getKey());
			}
		});

		final String br = CoreUtil.getPlatformLineSeparator();
		final String sep = " & ";

		if (results.isEmpty()) {
			// insert an empty row for this category
			final int length = mLatexTableHeaderCount + 2;
			for (int i = 0; i < length; ++i) {
				sb.append(sep);
			}
			sb.append("\\\\");
			sb.append(br);
			return;
		}

		boolean isFirst = true;

		for (final Entry<UltimateRunDefinition, ExtendedResult> result : results) {
			if (isFirst) {
				sb.append(sep);
				isFirst = false;
			} else {
				sb.append(sep).append(sep);
			}
			sb.append(removeInvalidCharsForLatex(result.getKey().getInputFileNames()));
			sb.append(sep);
			sb.append(removeInvalidCharsForLatex(result.getKey().getSettingsName()));
			sb.append(sep);

			ICsvProvider<String> csv =
					makePrintCsvProviderFromResults(Collections.singleton(result), mColumnDefinitions);

			csv = CsvUtils.projectColumn(csv,
					CoreUtil.select(mColumnDefinitions, new CoreUtil.IReduce<String, ColumnDefinition>() {
						@Override
						public String reduce(final ColumnDefinition entry) {
							return entry.getCsvColumnTitle();
						}
					}));

			csv = ColumnDefinitionUtil.reduceProvider(csv,
					CoreUtil.select(mColumnDefinitions, new CoreUtil.IReduce<Aggregate, ColumnDefinition>() {
						@Override
						public Aggregate reduce(final ColumnDefinition entry) {
							return entry.getManyRunsToOneRow();
						}
					}), mColumnDefinitions);

			csv = ColumnDefinitionUtil.makeHumanReadable(csv, mColumnDefinitions);

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

			final int length = mLatexTableHeaderCount;
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
}
