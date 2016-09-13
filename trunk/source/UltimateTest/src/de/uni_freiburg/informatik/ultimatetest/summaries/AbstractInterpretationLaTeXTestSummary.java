/*
 * Copyright (C) 2015 Christopher Dillo
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.AbstractInterpretationTestResultDecider.ActualResultType;
import de.uni_freiburg.informatik.ultimate.test.decider.AbstractInterpretationTestResultDecider.ExpectedResultType;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.OldTestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationLaTeXTestSummary extends OldTestSummary {

	protected final String mpathOfTrunk;
	
	protected final static TestResult[] s_testResultTypes = {TestResult.SUCCESS, TestResult.UNKNOWN, TestResult.FAIL};

	// array containing those expected result types we care about for our summary
	protected final static ExpectedResultType[] s_expectedResultTypes = {
		ExpectedResultType.SAFE, ExpectedResultType.UNSAFE
	};
	
	// statistics to determine average runtime and peak memory usage per result type (see s_expectedResultTypes)
	protected class ResultStatistics {
		protected static final int TIMECOUNT = 0;
		protected static final int MEMCOUNT = 1;
		protected static final int TIMESUM = 2;
		protected static final int MEMSUM = 3;
		protected static final int SIZE = 4;
		private final Map<ExpectedResultType, Long[]> mstatistics;
		
		protected ResultStatistics() {
			mstatistics = new HashMap<ExpectedResultType, Long[]>();
			for (final ExpectedResultType e : s_expectedResultTypes) {
				final Long[] eStats = new Long[SIZE];
				for (int i = 0; i < SIZE; i++) {
					eStats[i] = 0L;
				}
				mstatistics.put(e, eStats);
			}
		}
		
		/**
		 * @param resultType The result type for which these values apply
		 * @param runtime Runtime. Negative to ignore.
		 * @param peakMemory Peak memory usage. Negative to ignore.
		 */
		protected void addData(final ExpectedResultType resultType, final long runtime, final long peakMemory) {
			final Long[] typeStats = getData(resultType);
			if (typeStats != null) {
				if (runtime >= 0) {
					typeStats[TIMECOUNT]++;
					typeStats[TIMESUM] += runtime;
				}
				if (peakMemory >= 0) {
					typeStats[MEMCOUNT]++;
					typeStats[MEMSUM] += peakMemory;
				}
			}
		}
		
		protected Long[] getData(final ExpectedResultType resultType) {
			return mstatistics.get(resultType);
		}
		
		protected void addStats(final ResultStatistics stats, final boolean addTime, final boolean addMem) {
			if (stats == null) {
				return;
			}

			for (final ExpectedResultType e : s_expectedResultTypes) {
				final Long[] localStats = getData(e);
				final Long[] foreignStats = stats.getData(e);
				if (addTime) {
					localStats[TIMECOUNT] += foreignStats[TIMECOUNT];
					localStats[TIMESUM] += foreignStats[TIMESUM];
				}
				if (addMem) {
					localStats[MEMCOUNT] += foreignStats[MEMCOUNT];
					localStats[MEMSUM] += foreignStats[MEMSUM];
				}
			}
		}
	}

	// used for determining the table prefix
	protected static final String SVCOMP_FOLDER = "\\examples\\svcomp\\";

	public AbstractInterpretationLaTeXTestSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		
		mpathOfTrunk = TestUtil.getPathFromTrunk("");
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}
	
	@Override
	public String getDescriptiveLogName() {
		return "WermutTeXSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		final Map<TestResult, Integer> totalCounts = new HashMap<>();

		// cummulative stats for all tests
		final ResultStatistics totalStats = new ResultStatistics();

		/*
		 * Prints a table for use with the LaTeX-package "tabu" that can span over
		 * multiple pages and has the full linewidth (the X[l] column is flexible,
		 * stretching to fill the remaining space)
		 * 
		 * Following custom commands are used for better hlines:
		 * \newcommand{\strut}{\rule{0pt}{2.5ex}\ignorespaces}
		 * \newcommand{\dhline}{\hline\noalign{\vspace{2pt}}\hline}
		 */
		sb.append("\\begin{longtabu} to \\linewidth {cX[l]rccrr}").append(lineSeparator)
			.append("\t\\textbf{S} & \\textbf{File} & \\textbf{LoC} & \\textbf{ms} & \\textbf{MiB} \\\\").append(lineSeparator)
			.append("\t\\dhline \\endfirsthead").append(lineSeparator)
			.append("\t\\textbf{\\small S} & \\textbf{\\small File} & \\textbf{\\small LoC} & \\textbf{\\small ms} & \\textbf{\\small MiB} \\\\")
			.append(lineSeparator)
			.append("\t \\endhead").append(lineSeparator).append(lineSeparator);
		
		for (final TestResult result : s_testResultTypes) {
			int resultCategoryCount = 0;
			
			final String resultTag = testResultTag(result);
			
			for (final Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				
				final String[] categoryBlurb = entry.getKey().split(" ## ");
				final String tool = categoryBlurb.length > 0 ? categoryBlurb[0] : "---";
				final ExpectedResultType expectedResult = categoryBlurb.length > 1 ? expectedResultFromTag(categoryBlurb[1]) : null;
				final ActualResultType actualResult = categoryBlurb.length > 2 ? actualResultFromTag(categoryBlurb[2]) : null;
				
				// this summary only checks for abstract interpretation stuff!
				if (tool.startsWith("abstractinterpretation")) {
					sb.append("\t\\multicolumn{5}{c}{\\linestrut\\textbf{")
							.append(resultTag)
						.append(":}} \\\\").append(lineSeparator)
						.append("\t\\multicolumn{5}{c}{\\textbf{")
							.append("Expected ``")
								.append(expectedResult)
							.append(",'' analysis returned ``")
								.append(actualResult)
							.append("''")
						.append("}} \\\\").append(lineSeparator)
						.append("\t\\hline \\linestrut").append(lineSeparator);
	
					// stats for current actual-expected results pair
					final ResultStatistics currentStats = new ResultStatistics();
					
					for (final Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
						// \sffamily [SOURCE] & \small [FILENAME] & [LINES] & [RUNTIME] & [MAXMEM] \\
						
						// filename and source tag, file size
						String fileName = fileMsgPair.getKey();
						String tablePrefix = "---";
						final String fileLines = calculateNumberOfLines(fileName);
						if (fileName.startsWith(mpathOfTrunk + SVCOMP_FOLDER)) {
							tablePrefix = "S"; // file from SV-COMP
						} else {
							tablePrefix = "U"; // file from ULTIMATE
						}
						final String[] fileBlurb = fileName.split("\\\\");
						if (fileBlurb.length > 1) {
							fileName = fileBlurb[fileBlurb.length-1];
						}
						
						sb.append("\t\\sffamily ").append(tablePrefix)
							.append(" & \\small ").append(fileName).append(" & ")
							.append(fileLines).append(" & ");
						
						// runtime, max memory usage
						final String customMessage = fileMsgPair.getValue();
						if (customMessage != null && !customMessage.isEmpty()) {
							// customMessage: expected result, actual result, runtime, max memory usage, original result message
							final String[] message = customMessage.split(" ## ");
							if (message.length > 3) {
								sb.append(message[2]).append(" & ").append(message[3]).append(" \\\\");
								currentStats.addData(expectedResult, Long.parseLong(message[2]), Long.parseLong(message[3]));
							}
						} else {
							sb.append("--- & --- \\\\");
						}
						sb.append(lineSeparator);
					}
	
					final Long[] currentStatsNumbers = currentStats.getData(expectedResult);
					long runtimeSum, runtimeCount, memorySum, memoryCount;
					if (currentStatsNumbers == null) {
						runtimeSum = 0;
						runtimeCount = 0;
						memorySum = 0;
						memoryCount = 0;
					} else {
						runtimeSum = currentStatsNumbers[ResultStatistics.TIMESUM];
						runtimeCount = currentStatsNumbers[ResultStatistics.TIMECOUNT];
						memorySum = currentStatsNumbers[ResultStatistics.MEMSUM];
						memoryCount = currentStatsNumbers[ResultStatistics.MEMCOUNT];
					}
					final int localCount = entry.getValue().getCount();
					sb.append("\t\\hline \\linestrut & Count: ").append(localCount)
						.append(String.format(" & Avg: & %s & %s \\\\ %% RAW: %s / %s ms, %s / %s MiB",
								calculateAverage(runtimeSum, runtimeCount),
								calculateAverage(memorySum, memoryCount),
								runtimeSum, runtimeCount,
								memorySum, memoryCount)).append(lineSeparator)
						.append("\t\\dhline").append(lineSeparator);
					
					resultCategoryCount = resultCategoryCount + localCount;
					
					totalStats.addStats(currentStats, actualResult != ActualResultType.TIMEOUT, true);
				}
			}

			totalCounts.put(result, resultCategoryCount);
		}

		sb.append("\\end{longtabu}").append(lineSeparator).append(lineSeparator);

		sb.append("\\begin{longtabu} to \\linewidth {X[l]r}").append(lineSeparator)
			.append("\t\\multicolumn{2}{c}{\\textbf{Statistics}} \\\\").append(lineSeparator)
			.append("\t\\textbf{Result} & \\textbf{Count} \\\\").append(lineSeparator)
			.append("\t\\dhline \\linestrut").append(lineSeparator);
		int totalCount = 0;
		for (final TestResult result : s_testResultTypes) {
			sb.append("\t").append(testResultTag(result)).append(" & ").append(totalCounts.get(result)).append(" \\\\").append(lineSeparator);
			totalCount += totalCounts.get(result);
		}
		sb.append("\t\\hline \\linestrut Total & ").append(totalCount).append(" \\\\").append(lineSeparator);
		
		for (final ExpectedResultType e : s_expectedResultTypes) {
			final Long[] totalStatsNumbers = totalStats.getData(e);
			long runtimeSum, runtimeCount, memorySum, memoryCount;
			if (totalStatsNumbers == null) {
				runtimeSum = 0;
				runtimeCount = 0;
				memorySum = 0;
				memoryCount = 0;
			} else {
				runtimeSum = totalStatsNumbers[ResultStatistics.TIMESUM];
				runtimeCount = totalStatsNumbers[ResultStatistics.TIMECOUNT];
				memorySum = totalStatsNumbers[ResultStatistics.MEMSUM];
				memoryCount = totalStatsNumbers[ResultStatistics.MEMCOUNT];
			}
			
			sb.append("\t\\dhline \\linestrut").append(lineSeparator)
				.append(String.format("\t Average runtime for %s & %s~ms \\\\ %% RAW: %s / %s ms",
					e, calculateAverage(runtimeSum, runtimeCount), runtimeSum, runtimeCount)).append(lineSeparator)
				.append(String.format("\t Average peak memory usage for %s & %s~MiB \\\\ %% RAW: %s / %s MiB",
					e, calculateAverage(memorySum, memoryCount), memorySum, memoryCount)).append(lineSeparator);
		}
		sb.append("\t\\dhline \\\\").append(lineSeparator).append("\\end{longtabu}").append(lineSeparator);
		
		return sb.toString();
	}
	
	/**
	 * @param fileName
	 * @return Number of lines in the file associated to fileName
	 */
	protected String calculateNumberOfLines(final String fileName) {
		String result = "---";
		try {
			final LineNumberReader reader = new LineNumberReader(new FileReader(new File(fileName)));
			reader.skip(Long.MAX_VALUE);
			result = String.format("%d", reader.getLineNumber());
			reader.close();
		} catch (final IOException e) {
			e.printStackTrace();
		}
		return result;
	}

	protected String calculateAverage(final long sum, final long count) {
		if (count == 0)
		 {
			return "---"; // No count, no average.
		}
		return String.format("%d", Math.round(((double) sum) / ((double) count)));
	}
	
	protected String testResultTag(final TestResult result) {
		switch (result) {
		case SUCCESS :
			return "Successfully verified";
		case UNKNOWN :
			return "Unable to verify";
		case FAIL :
			return "Failed to verify";
		default:
			return "Something went wrong";
		}
	}

	protected String actualResultTag(final ActualResultType result) {
		if (result == null) {
			return "---";
		}
		
		switch (result) {
		case SAFE :
			return "$\\checkmark$";
		case UNSAFE :
			return "$\\times$";
		case UNKNOWN :
		case SYNTAX_ERROR :
		case TIMEOUT :
		case UNSUPPORTED_SYNTAX :
		case EXCEPTION_OR_ERROR :
			return "?";
		case NO_RESULT :
		default :
			return "---";
		}
	}
	
	protected String expectedResultTag(final ExpectedResultType result) {
		if (result == null) {
			return "---";
		}
		
		switch (result) {
		case SAFE :
			return "$\\checkmark$";
		case UNSAFE :
		case SYNTAXERROR :
			return "$\\times$";
		case NOANNOTATION :
			return "?";
		default :
			return "---";
		}
	}

	protected ActualResultType actualResultFromTag(final String resultTag) {
		if (resultTag == null) {
			return ActualResultType.NO_RESULT;
		}
		
		switch (resultTag) {
		case "SAFE" :
			return ActualResultType.SAFE;
		case "UNSAFE" :
			return ActualResultType.UNSAFE;
		case "UNKNOWN" :
			return ActualResultType.UNKNOWN;
		case "SYNTAX_ERROR" :
			return ActualResultType.SYNTAX_ERROR;
		case "TIMEOUT" :
			return ActualResultType.TIMEOUT;
		case "UNSUPPORTED_SYNTAX" :
			return ActualResultType.UNSUPPORTED_SYNTAX;
		case "EXCEPTION_OR_ERROR" :
			return ActualResultType.EXCEPTION_OR_ERROR;
		case "NO_RESULT" :
			return ActualResultType.NO_RESULT;
		default :
			return null;
		}
	}
	
	protected ExpectedResultType expectedResultFromTag(final String resultTag) {
		if (resultTag == null) {
			return ExpectedResultType.NOANNOTATION;
		}
		
		switch (resultTag) {
		case "SAFE" :
			return ExpectedResultType.SAFE;
		case "UNSAFE" :
			return ExpectedResultType.UNSAFE;
		case "SYNTAXERROR" :
			return ExpectedResultType.SYNTAXERROR;
		case "NOANNOTATION" :
			return ExpectedResultType.NOANNOTATION;
		default :
			return null;
		}
	}
}
