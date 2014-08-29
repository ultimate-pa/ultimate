/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.abstractinterpretation.AbstractInterpretationTestResultDecider.ActualResultType;
import de.uni_freiburg.informatik.ultimatetest.abstractinterpretation.AbstractInterpretationTestResultDecider.ExpectedResultType;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationComparisonTestSummary extends AbstractInterpretationLaTeXTestSummary {

	private static final int EXP = 0;
	private static final int ACT = 1;
	private static final int TIM = 2;
	private static final int MEM = 3;
	private static final int SIZE = 4;
	
	// array containing those actual result types we care about for our summary
	protected final static ActualResultType[] s_actualResultTypes = {
		ActualResultType.SAFE, ActualResultType.UNSAFE, ActualResultType.UNKNOWN
	};

	public AbstractInterpretationComparisonTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return "AbsIntCompSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {

		Map<String, String> fileToLineCount = new HashMap<String, String>();
		// map: filename -> (LoC, expected, actual, runtime, memory)
		Map<String, String[]> fileToWermutResult = new HashMap<String, String[]>();
		Map<String, String[]> fileToAutomizerResult = new HashMap<String, String[]>();
		
		// map: actual result tag -> statistics
		Map<String, ResultStatistics> wermutResultStatistics = new HashMap<String, ResultStatistics>();
		Map<String, ResultStatistics> automizerResultStatistics = new HashMap<String, ResultStatistics>();
		 
		/* ###### STEP 1 : COLLECT RESULTS FROM ABSTRACT INTERPRETATIO AND AUTOMIZER ###### */
		
		for (TestResult result : s_testResultTypes) {
			
			for (Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				String[] categoryBlurb = entry.getKey().split(" ## ");
				String tool = categoryBlurb.length > 0 ? categoryBlurb[0] : "---";
				ExpectedResultType expectedResult = categoryBlurb.length > 1 ? expectedResultFromTag(categoryBlurb[1]) : null;
				ActualResultType actualResult = categoryBlurb.length > 2 ? actualResultFromTag(categoryBlurb[2]) : null;
				String tagForExpectedResult = expectedResultTag(expectedResult);
				String tagForActualResult = actualResultTag(actualResult);
				
				// compare tool to the string Plug-Ins add to IResult for identification
				Map<String, String[]> fileToResult = null;
				Map<String, ResultStatistics> toolResultStatistics = null;
				if (tool.equals("AbstractInterpretation")) {
					fileToResult = fileToWermutResult;
					toolResultStatistics = wermutResultStatistics;
				} else if (tool.equals("TraceAbstraction")) {
					fileToResult = fileToAutomizerResult;
					toolResultStatistics = automizerResultStatistics;
				}
				
				if ((fileToResult != null) && (toolResultStatistics != null)) {
					ResultStatistics statistics = toolResultStatistics.get(tagForActualResult);
					if (statistics == null) {
						statistics = new ResultStatistics();
						toolResultStatistics.put(tagForActualResult, statistics);
					}
					
					for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
						// filename without path
						String fullFileName = fileMsgPair.getKey();
						String[] fileBlurb = fullFileName.split("\\\\");
						String fileName = fileBlurb[fileBlurb.length-1];
						if (!fileToLineCount.containsKey(fileName))
							fileToLineCount.put(fileName, calculateNumberOfLines(fullFileName));
						
						// expected and actual result
						String[] resultData = new String[SIZE];
						resultData[EXP] = tagForExpectedResult;
						resultData[ACT] = tagForActualResult;

						// runtime, max memory usage
						resultData[TIM] = "---";
						resultData[MEM] = "---";
						String customMessage = fileMsgPair.getValue();
						if (customMessage != null && !customMessage.isEmpty()) {
							// customMessage: expected result, actual result, runtime, max memory usage, original result message
							String[] message = customMessage.split(" ## ");
							if (message.length > 3) {
								resultData[TIM] = message[2];
								resultData[MEM] = message[3];
								statistics.addData(expectedResult,
										actualResult == ActualResultType.TIMEOUT ? -1L : Long.parseLong(resultData[TIM]),
										Long.parseLong(resultData[MEM]));
								// timeouts are not counted for the average values
							}
						}
						fileToResult.put(fileName, resultData);
					}
				}
			}
		}
		 
		/* ###### STEP 2 : PRINT TABLE COMPARING RESULTS ###### */
		
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		
		/*
		 * Main table: File list comparing abstract interpretation to automizer
		 * 
		 * 	                                 ||        abstract interpretation        ||               automizer               ||
		 *	filename | LoC | expected result || actual result | runtime | peak memory || actual result | runtime | peak memory ||
		 *
		 * The LaTeX "longtabu" environment is part of the "tabu" package.
		 * 
		 * Following custom commands are used for better hlines:
		 * \newcommand{\strut}{\rule{0pt}{2.5ex}\ignorespaces}
		 * \newcommand{\dhline}{\hline\noalign{\vspace{2pt}}\hline}
		 */

		sb.append("{\\small").append(lineSeparator)
			.append("\\begin{longtabu} to \\linewidth {X[l]rc|crr|crr}").append(lineSeparator)
			.append("\t\\multicolumn{3}{c|}{} & \\multicolumn{3}{c|}{\\textbf{Abs. Int.}}")
				.append(" & \\multicolumn{3}{c}{\\textbf{Automizer}} \\\\").append(lineSeparator)
			.append("\t\\textbf{File} & \\textbf{LoC} & \\textbf{E} & \\textbf{A} & \\textbf{ms} & \\textbf{MiB}")
				.append(" & \\textbf{A} & \\textbf{ms} & \\textbf{MiB} \\\\").append(lineSeparator)
			.append("\t\\dhline \\endfirsthead").append(lineSeparator)
			.append("\t\\textbf{File} & \\textbf{LoC} & \\textbf{E} & \\textbf{A} & \\textbf{ms} & \\textbf{MiB}")
			.append(" & \\textbf{A} & \\textbf{ms} & \\textbf{MiB} \\\\").append(lineSeparator)
			.append("\t \\endhead").append(lineSeparator).append("\t\\linestrut").append(lineSeparator);
		
		// list all files in alphabetical order
		List<String> files = new ArrayList<String>(fileToLineCount.keySet());
		Collections.sort(files);
		for (String fileName : files) {
			String lineCount = fileToLineCount.get(fileName);
			String[] wermutResult = fileToWermutResult.get(fileName);
			String[] automizerResult = fileToAutomizerResult.get(fileName);
			
			// if no matching Abstract Interpretation result should exist: empty table entries
			if (wermutResult == null) {
				wermutResult = new String[SIZE];
				wermutResult[EXP] = "---";
				wermutResult[ACT] = "---";
				wermutResult[TIM] = "---";
				wermutResult[MEM] = "---";
			}
			
			// if no matching Automizer result should exist: empty table entries
			if (automizerResult == null) {
				automizerResult = new String[SIZE];
				automizerResult[EXP] = "---";
				automizerResult[ACT] = "---";
				automizerResult[TIM] = "---";
				automizerResult[MEM] = "---";
			}
			
			sb.append("\t").append(fileName).append(" & ")
				.append(lineCount).append(" & ")
				.append(wermutResult[EXP]).append(" & ")
				.append(wermutResult[ACT]).append(" & ")
				.append(wermutResult[TIM]).append(" & ")
				.append(wermutResult[MEM]).append(" & ")
				.append(automizerResult[ACT]).append(" & ")
				.append(automizerResult[TIM]).append(" & ")
				.append(automizerResult[MEM]).append(" \\\\ ")
				.append(lineSeparator);
		}
		
		sb.append("\t\\dhline").append(lineSeparator).append("\\end{longtabu}")
			.append(lineSeparator).append("}")
			.append(lineSeparator).append(lineSeparator).append(lineSeparator);

		/*
		 * Additional table: Statistics
		 * 
		 * Expected result         ||                 SAFE                 ||                UNSAFE                ||
		 * Actual result           || Safe | Unsafe | Unknown | Time | Mem || Safe | Unsafe | Unknown | Time | Mem ||
		 * Abstract Interpretation ||    # |      # |       # |   ms | MiB ||    # |      # |       # |   ms | MiB ||
		 * Automizer               ||    # |      # |       # |   ms | MiB ||    # |      # |       # |   ms | MiB ||
		 * 
		 * 
		 *                         || Expected result ||        SAFE        ||       UNSAFE       ||       TOTAL        ||
		 *           Tool          ||  Actual result  || Count | Time | Mem || Count | Time | Mem || Count | Time | Mem ||
		 * ===============================================================================================================
		 * Abstract Interpretation || Safe            ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         || Unsafe          ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         || Unknown         ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         ---------------------------------------------------------------------------------------
		 *                         || Total           ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 * ===============================================================================================================
		 * Automizer               || Safe            ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         || Unsafe          ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         || Unknown         ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 *                         ---------------------------------------------------------------------------------------
		 *                         || Total           ||     # |   ms | MiB ||     # |   ms | MiB ||     # |   ms | MiB ||
		 * ===============================================================================================================
		 */

		sb.append("\\begin{longtabu} to \\linewidth {X[l]|c|rrr|rrr|rrr}").append(lineSeparator)
			.append("\t & & \\multicolumn{3}{c|}{\\textbf{Safe}} & \\multicolumn{3}{c|}{\\textbf{Unsafe}}")
			.append(" & \\multicolumn{3}{c}{\\textbf{Total}} \\\\")
			.append(lineSeparator).append("\t\\hline\\linestrut").append(lineSeparator)
			.append("\t\\textbf{Tool} & & \\textbf{\\#} & \\textbf{ms} & \\textbf{MiB} & \\textbf{\\#}")
			.append(" & \\textbf{ms} & \\textbf{MiB} & \\textbf{\\#} & \\textbf{ms} & \\textbf{MiB} \\\\")
			.append(lineSeparator).append("\t\\dhline\\linestrut").append(lineSeparator);
		
		Map<String, Map<String, ResultStatistics>> toolResultStatisticsMap = new LinkedHashMap<String, Map<String, ResultStatistics>>();
		toolResultStatisticsMap.put("Abstract Interpretation", wermutResultStatistics);
		toolResultStatisticsMap.put("Automizer", automizerResultStatistics);
		for (String tool : toolResultStatisticsMap.keySet()) {
			sb.append("\t\\linestrut").append(lineSeparator);
			
			// actual result tag -> result statistics
			Map<String, ResultStatistics> toolResultStatistics = toolResultStatisticsMap.get(tool);

			ResultStatistics cummulative = new ResultStatistics();
			for (ActualResultType a : s_actualResultTypes) {
				ResultStatistics statistics = toolResultStatistics.get(actualResultTag(a));
				sb.append("\t").append((a == s_actualResultTypes[0]) ? tool : "").append(" & ")
					.append(actualResultTag(a));
				if (statistics == null) {
					sb.append(" & 0 & --- & --- & 0 & --- & --- & 0 & --- & --- \\\\");
				} else {
					printResultStatistics(sb, statistics);
					cummulative.addStats(statistics, true, true);
				}
				sb.append(lineSeparator);
			}
			// cummulative stats
			sb.append("\t\\hline\\linestrut & $\\sum$ ");
			printResultStatistics(sb, cummulative);
			sb.append(lineSeparator)
				.append("\t\\dhline").append(lineSeparator);
		}
		
		sb.append("\\end{longtabu}").append(lineSeparator);
		
		return sb.toString();
	}
	
	protected void printResultStatistics(StringBuilder target, ResultStatistics statistics) {
		long timeSum = 0, timeCount = 0, memSum = 0, memCount = 0;
		StringBuilder rawData = new StringBuilder();
		for (ExpectedResultType e : s_expectedResultTypes) {
			Long[] data = statistics.getData(e);
			if (data == null) {
				target.append(" & 0 & --- & ---");
			} else {
				target.append(String.format(" & %s & %s & %s",
						data[ResultStatistics.MEMCOUNT],
						calculateAverage(data[ResultStatistics.TIMESUM], data[ResultStatistics.TIMECOUNT]),
						calculateAverage(data[ResultStatistics.MEMSUM], data[ResultStatistics.MEMCOUNT])));
				rawData.append(String.format(" %s: %s / %s ms, %s / %s MiB %%", e,
						data[ResultStatistics.TIMESUM], data[ResultStatistics.TIMECOUNT],
						data[ResultStatistics.MEMSUM], data[ResultStatistics.MEMCOUNT]));
				timeSum += data[ResultStatistics.TIMESUM];
				timeCount += data[ResultStatistics.TIMECOUNT];
				memSum += data[ResultStatistics.MEMSUM];
				memCount += data[ResultStatistics.MEMCOUNT];
			}
		}
		// totals
		target.append(String.format(" & %s & %s & %s",
				memCount, calculateAverage(timeSum, timeCount), calculateAverage(memSum, memCount)));
		rawData.append(String.format(" %s / %s ms, %s / %s MiB", timeSum, timeCount, memSum, memCount));
		target.append(" \\\\ %% RAW:").append(rawData);
	}
}
