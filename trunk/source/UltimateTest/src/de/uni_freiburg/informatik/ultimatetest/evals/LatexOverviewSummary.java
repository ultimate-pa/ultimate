package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.evals.ColumnDefinition.Aggregate;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class LatexOverviewSummary extends BaseCsvProviderSummary {

	private final int mLatexTableHeaderCount;

	/**
	 * Create a summary that prints a file containing LaTex table for each
	 * toolchain. The table groups test runs by folder name and compares them
	 * against different setting files.
	 * 
	 * The values result from benchmark providers collected during the Ultimate
	 * runs.
	 * 
	 * @param ultimateTestSuite
	 *            To which testsuite belongs this summary?
	 * @param benchmarks
	 *            A list of benchmark types that should be included in the
	 *            table.
	 * @param columnDefinitions
	 *            An array of column definitions that specify how the benchmark
	 *            results should be processed (values as well as strings)
	 */
	public LatexOverviewSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);

		mLatexTableHeaderCount = CoreUtil.reduce(mColumnDefinitions,
				new CoreUtil.IMapReduce<Integer, ColumnDefinition>() {
					@Override
					public Integer reduce(Integer lastValue, ColumnDefinition entry) {
						if (lastValue == null) {
							lastValue = 0;
						}
						return entry.getLatexTableTitle() != null ? lastValue + 1 : lastValue;
					}
				});
	}

	@Override
	public String getSummaryLog() {
		StringBuilder sb = new StringBuilder();
		PartitionedResults results = partitionResults(mResults.entrySet());

		makeTables(sb, results);

		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}

	private void makeTables(StringBuilder sb, PartitionedResults results) {

		Set<String> tools = CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getToolchain().getName();
			}
		});

		String br = CoreUtil.getPlatformLineSeparator();

		appendPreamble(sb, br);

		for (final String tool : tools) {
			// make table header
			sb.append("\\begin{table}").append(br);
			sb.append("\\centering").append(br);
			sb.append("\\resizebox{\\linewidth}{!}{%").append(br);
			sb.append("\\begin{tabu} to \\linewidth {lcllc");
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
			for (ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getLatexTableTitle() == null) {
					continue;
				}
				sb.append("  \\header{");
				sb.append(removeInvalidCharsForLatex(cd.getLatexTableTitle()));
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
			PartitionedResults resultsPerTool = partitionResults(CoreUtil.where(results.All,
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().getName().equals(tool);
						}
					}));
			makeTableBody(sb, resultsPerTool, tool);

			// end table
			sb.append("\\end{tabu}}").append(br);
			sb.append("\\caption{Results for ").append(removeInvalidCharsForLatex(tool)).append(".}").append(br);
			sb.append("\\end{table}").append(br);
		}

		// append finishing code
		appendEnd(sb, br);
	}

	private void appendEnd(StringBuilder sb, String br) {
		sb.append("\\end{document}").append(br);
	}

	private void appendPreamble(StringBuilder sb, String br) {
		// append preamble
		sb.append("\\documentclass[a4paper]{article}").append(br);
		sb.append("\\usepackage[a4paper, margin=1.5cm, top=1.1cm]{geometry}").append(br);
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

	private void makeTableBody(StringBuilder sb, PartitionedResults results, String toolname) {
		// make header

		Set<String> folders = CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getInput().getParentFile().getName();
			}
		});

		int i = 0;
		for (final String folder : folders) {
			PartitionedResults resultsPerFolder = partitionResults(CoreUtil.where(results.All,
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getInput().getParentFile().getName().equals(folder);
						}
					}));
			i++;
			makeFolderRow(sb, resultsPerFolder, folder, i >= folders.size());
		}

	}

	private void makeFolderRow(StringBuilder sb, PartitionedResults results, String folder, boolean last) {
		String br = CoreUtil.getPlatformLineSeparator();
		final int resultRows = 4;

		List<String> variants = new ArrayList<>(CoreUtil.selectDistinct(results.All, new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getSettings().getName();
			}
		}));

		// folder name
		sb.append("\\multirow{");
		sb.append(variants.size() * resultRows);
		sb.append("}{*}{\\folder{");
		sb.append(folder);
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
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> completed = new ArrayList<>();
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

	private void makeVariantEntry(StringBuilder sb, Collection<Entry<UltimateRunDefinition, ExtendedResult>> current,
			final String variant, boolean isFirst) {

		Collection<Entry<UltimateRunDefinition, ExtendedResult>> results = CoreUtil.where(current,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return entry.getKey().getSettings().getName().equals(variant);
					}
				});

		String br = CoreUtil.getPlatformLineSeparator();
		String sep = " & ";

		if (isFirst) {
			sb.append(sep);
		} else {
			sb.append(sep).append(sep).append(sep);
		}
		sb.append(removeInvalidCharsForLatex(variant));
		sb.append(sep);

		ICsvProvider<String> csv = makePrintCsvProviderFromResults(results, mColumnDefinitions);

		csv = CsvUtils.projectColumn(csv,
				CoreUtil.select(mColumnDefinitions, new CoreUtil.IReduce<String, ColumnDefinition>() {
					@Override
					public String reduce(ColumnDefinition entry) {
						return entry.getColumnToKeep();
					}
				}));

		csv = ColumnDefinitionUtil.reduceProvider(csv,
				CoreUtil.select(mColumnDefinitions, new CoreUtil.IReduce<Aggregate, ColumnDefinition>() {
					@Override
					public Aggregate reduce(ColumnDefinition entry) {
						return entry.getManyRunsToOneRow();
					}
				}), mColumnDefinitions);

		csv = ColumnDefinitionUtil.makeHumanReadable(csv, mColumnDefinitions);
		csv = CsvUtils.addColumn(csv, "Count", 0, Arrays.asList(new String[] { Integer.toString(results.size()) }));

		// make list of indices to ignore idx -> true / false
		boolean[] idx = new boolean[csv.getColumnTitles().size()];
		// because of count
		idx[0] = true;
		for (int i = 1; i < idx.length; ++i) {
			String currentHeader = csv.getColumnTitles().get(i);
			for (ColumnDefinition cd : mColumnDefinitions) {
				if (cd.getColumnToKeep().equals(currentHeader)) {
					idx[i] = (cd.getLatexTableTitle() != null);
					break;
				}
			}
		}

		// one more because of Count
		int length = mLatexTableHeaderCount + 1;
		int i = 0;
		List<String> row = csv.getRow(0);
		if (row == null || row.size() == 0) {
			// no results in this category, just fill with empty fields
			for (; i < length; ++i) {
				sb.append(sep);
			}
		} else {
			for (String cell : row) {
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

	private boolean isInvalidForLatex(String cell) {
		return cell == null || cell.contains("[");
	}

	private String removeInvalidCharsForLatex(String cell) {
		return cell.replace("_", "\\_");
	}
}
