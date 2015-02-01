package de.uni_freiburg.informatik.ultimatetest.evals;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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
public class LatexDetailedSummary extends BaseCsvProviderSummary {

	private final int mLatexTableHeaderCount;

	public LatexDetailedSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
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

		try {
			makeTables(sb, results);
		} catch (Error e) {
			return "";
		}

		return sb.toString();
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}

	private void makeTables(StringBuilder sb, PartitionedResults results) {

		final int additionalHeaders = 4;

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
			sb.append("\\begin{tabu} to \\linewidth {llll");
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
			sb.append(additionalHeaders + mLatexTableHeaderCount);
			sb.append("}").append(br);

			// make table body
			PartitionedResults resultsPerTool = partitionResults(CoreUtil.where(results.All,
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().getName().equals(tool);
						}
					}));
			makeTableBody(sb, resultsPerTool, tool, additionalHeaders);

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

	private void makeTableBody(StringBuilder sb, PartitionedResults results, String toolname, int additionalTableHeaders) {
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
			makeFolderRow(sb, resultsPerFolder, folder, i >= folders.size(), additionalTableHeaders);
		}
	}

	private void makeFolderRow(StringBuilder sb, PartitionedResults results, String folder, boolean last,
			int additionalTableHeaders) {
		String br = CoreUtil.getPlatformLineSeparator();
		final int additionalHeaders = additionalTableHeaders;

		List<File> files = new ArrayList<>(CoreUtil.selectDistinct(results.All, new IMyReduce<File>() {
			@Override
			public File reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getInput();
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
		sb.append(folder);
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

	private void makeFileEntry(StringBuilder sb, Collection<Entry<UltimateRunDefinition, ExtendedResult>> current,
			final List<File> files) {

		List<Entry<UltimateRunDefinition, ExtendedResult>> results = new ArrayList<>(CoreUtil.where(current,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						return files.contains(entry.getKey().getInput());
					}
				}));

		Collections.sort(results, new Comparator<Entry<UltimateRunDefinition, ExtendedResult>>() {
			@Override
			public int compare(Entry<UltimateRunDefinition, ExtendedResult> o1,
					Entry<UltimateRunDefinition, ExtendedResult> o2) {
				int nameCompare = o1.getKey().getInput().compareTo(o2.getKey().getInput());
				if (nameCompare == 0) {
					return o1.getKey().getSettings().getName().compareTo(o2.getKey().getSettings().getName());
				}
				return nameCompare;
			}
		});

		String br = CoreUtil.getPlatformLineSeparator();
		String sep = " & ";

		if (results.size() == 0) {
			// insert an empty row for this category
			int length = mLatexTableHeaderCount + 2;
			for (int i = 0; i < length; ++i) {
				sb.append(sep);
			}
			sb.append("\\\\");
			sb.append(br);
			return;
		}

		boolean isFirst = true;

		for (Entry<UltimateRunDefinition, ExtendedResult> result : results) {
			if (isFirst) {
				sb.append(sep);
				isFirst = false;
			} else {
				sb.append(sep).append(sep);
			}
			sb.append(removeInvalidCharsForLatex(result.getKey().getInput().getName()));
			sb.append(sep);
			sb.append(removeInvalidCharsForLatex(result.getKey().getSettings().getName()));
			sb.append(sep);

			ICsvProvider<String> csv = makePrintCsvProviderFromResults(Collections.singleton(result),
					mColumnDefinitions);

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

			int length = mLatexTableHeaderCount;
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
	}

	private boolean isInvalidForLatex(String cell) {
		return cell == null || cell.contains("[");
	}

	private String removeInvalidCharsForLatex(String cell) {
		return cell.replace("_", "\\_");
	}
}
