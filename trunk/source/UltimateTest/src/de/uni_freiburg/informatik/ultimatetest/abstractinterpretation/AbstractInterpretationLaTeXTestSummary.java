/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.abstractinterpretation.AbstractInterpretationTestResultDecider.ActualResultType;
import de.uni_freiburg.informatik.ultimatetest.abstractinterpretation.AbstractInterpretationTestResultDecider.ExpectedResultType;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationLaTeXTestSummary extends TestSummary {

	protected final String m_pathOfTrunk;
	
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
		private Map<ExpectedResultType, Long[]> m_statistics;
		
		protected ResultStatistics() {
			m_statistics = new HashMap<ExpectedResultType, Long[]>();
			for (ExpectedResultType e : s_expectedResultTypes) {
				Long[] eStats = new Long[SIZE];
				for (int i = 0; i < SIZE; i++)
					eStats[i] = 0L;
				m_statistics.put(e, eStats);
			}
		}
		
		/**
		 * @param resultType The result type for which these values apply
		 * @param runtime Runtime. Negative to ignore.
		 * @param peakMemory Peak memory usage. Negative to ignore.
		 */
		protected void addData(ExpectedResultType resultType, long runtime, long peakMemory) {
			Long[] typeStats = getData(resultType);
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
		
		protected Long[] getData(ExpectedResultType resultType) {
			return m_statistics.get(resultType);
		}
		
		protected void addStats(ResultStatistics stats, boolean addTime, boolean addMem) {
			if (stats == null) return;

			for (ExpectedResultType e : s_expectedResultTypes) {
				Long[] localStats = getData(e);
				Long[] foreignStats = stats.getData(e);
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
	protected final String m_svcompFolder = "\\examples\\svcomp\\";

	public AbstractInterpretationLaTeXTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
		
		m_pathOfTrunk = Util.getPathFromTrunk("");
	}

	@Override
	public String getFilenameExtension() {
		return ".tex";
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return "WermutTeXSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		Map<TestResult, Integer> totalCounts = new HashMap<>();

		// cummulative stats for all tests
		ResultStatistics totalStats = new ResultStatistics();

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
		
		for (TestResult result : s_testResultTypes) {
			int resultCategoryCount = 0;
			
			String resultTag = testResultTag(result);
			
			for (Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				
				String[] categoryBlurb = entry.getKey().split(" ## ");
				String tool = categoryBlurb.length > 0 ? categoryBlurb[0] : "---";
				ExpectedResultType expectedResult = categoryBlurb.length > 1 ? expectedResultFromTag(categoryBlurb[1]) : null;
				ActualResultType actualResult = categoryBlurb.length > 2 ? actualResultFromTag(categoryBlurb[2]) : null;
				
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
					ResultStatistics currentStats = new ResultStatistics();
					
					for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
						// \sffamily [SOURCE] & \small [FILENAME] & [LINES] & [RUNTIME] & [MAXMEM] \\
						
						// filename and source tag, file size
						String fileName = fileMsgPair.getKey();
						String tablePrefix = "---";
						String fileLines = calculateNumberOfLines(fileName);
						if (fileName.startsWith(m_pathOfTrunk + m_svcompFolder)) {
							tablePrefix = "S"; // file from SV-COMP
						} else {
							tablePrefix = "U"; // file from ULTIMATE
						}
						String[] fileBlurb = fileName.split("\\\\");
						if (fileBlurb.length > 1)
							fileName = fileBlurb[fileBlurb.length-1];
						
						sb.append("\t\\sffamily ").append(tablePrefix)
							.append(" & \\small ").append(fileName).append(" & ")
							.append(fileLines).append(" & ");
						
						// runtime, max memory usage
						String customMessage = fileMsgPair.getValue();
						if (customMessage != null && !customMessage.isEmpty()) {
							// customMessage: expected result, actual result, runtime, max memory usage, original result message
							String[] message = customMessage.split(" ## ");
							if (message.length > 3) {
								sb.append(message[2]).append(" & ").append(message[3]).append(" \\\\");
								currentStats.addData(expectedResult, Long.parseLong(message[2]), Long.parseLong(message[3]));
							}
						} else {
							sb.append("--- & --- \\\\");
						}
						sb.append(lineSeparator);
					}
	
					Long[] currentStatsNumbers = currentStats.getData(expectedResult);
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
					int localCount = entry.getValue().getCount();
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
		for (TestResult result : s_testResultTypes) {
			sb.append("\t").append(testResultTag(result)).append(" & ").append(totalCounts.get(result)).append(" \\\\").append(lineSeparator);
			totalCount += totalCounts.get(result);
		}
		sb.append("\t\\hline \\linestrut Total & ").append(totalCount).append(" \\\\").append(lineSeparator);
		
		for (ExpectedResultType e : s_expectedResultTypes) {
			Long[] totalStatsNumbers = totalStats.getData(e);
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
	protected String calculateNumberOfLines(String fileName) {
		String result = "---";
		try {
			LineNumberReader reader = new LineNumberReader(new FileReader(new File(fileName)));
			reader.skip(Long.MAX_VALUE);
			result = String.format("%d", reader.getLineNumber());
			reader.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return result;
	}

	protected String calculateAverage(long sum, long count) {
		if (count == 0) return "---"; // No count, no average.
		return String.format("%d", Math.round(((double) sum) / ((double) count)));
	}
	
	protected String testResultTag(TestResult result) {
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

	protected String actualResultTag(ActualResultType result) {
		if (result == null) return "---";
		
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
	
	protected String expectedResultTag(ExpectedResultType result) {
		if (result == null) return "---";
		
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

	protected ActualResultType actualResultFromTag(String resultTag) {
		if (resultTag == null) return ActualResultType.NO_RESULT;
		
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
	
	protected ExpectedResultType expectedResultFromTag(String resultTag) {
		if (resultTag == null) return ExpectedResultType.NOANNOTATION;
		
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
