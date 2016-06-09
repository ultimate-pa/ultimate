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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.AbstractInterpretationTestResultDecider.ActualResultType;
import de.uni_freiburg.informatik.ultimate.test.decider.AbstractInterpretationTestResultDecider.ExpectedResultType;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;

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
	public String getDescriptiveLogName() {
		return "WermutCompSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {

		final Map<String, String> fileToLineCount = new HashMap<String, String>();
		// map: filename -> (LoC, expected, actual, runtime, memory)
		final Map<String, String[]> fileToWermutResult = new HashMap<String, String[]>();
		final Map<String, String[]> fileToAutomizerResult = new HashMap<String, String[]>();
		
		// map: actual result tag -> statistics
		final Map<String, ResultStatistics> wermutResultStatistics = new HashMap<String, ResultStatistics>();
		final Map<String, ResultStatistics> automizerResultStatistics = new HashMap<String, ResultStatistics>();
		 
		/* ###### STEP 1 : COLLECT RESULTS FROM ABSTRACT INTERPRETATIO AND AUTOMIZER ###### */
		
		for (final TestResult result : s_testResultTypes) {
			
			for (final Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
				final String[] categoryBlurb = entry.getKey().split(" ## ");
				final String tool = categoryBlurb.length > 0 ? categoryBlurb[0] : "---";
				final ExpectedResultType expectedResult = categoryBlurb.length > 1 ? expectedResultFromTag(categoryBlurb[1]) : null;
				final ActualResultType actualResult = categoryBlurb.length > 2 ? actualResultFromTag(categoryBlurb[2]) : null;
				final String tagForExpectedResult = expectedResultTag(expectedResult);
				final String tagForActualResult = actualResultTag(actualResult);
				
				// compare tool to the string Plug-Ins add to IResult for identification
				Map<String, String[]> fileToResult = null;
				Map<String, ResultStatistics> toolResultStatistics = null;
				if (tool.startsWith("abstractinterpretation")) {
					fileToResult = fileToWermutResult;
					toolResultStatistics = wermutResultStatistics;
				} else if (tool.startsWith("automizer")) {
					fileToResult = fileToAutomizerResult;
					toolResultStatistics = automizerResultStatistics;
				}
				
				if ((fileToResult != null) && (toolResultStatistics != null)) {
					ResultStatistics statistics = toolResultStatistics.get(tagForActualResult);
					if (statistics == null) {
						statistics = new ResultStatistics();
						toolResultStatistics.put(tagForActualResult, statistics);
					}
					
					for (final Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
						// filename without path
						final String fullFileName = fileMsgPair.getKey();
						final String[] fileBlurb = fullFileName.split("\\\\");
						final String fileName = fileBlurb[fileBlurb.length-1];
						if (!fileToLineCount.containsKey(fileName)) {
							fileToLineCount.put(fileName, calculateNumberOfLines(fullFileName));
						}
						
						// expected and actual result
						final String[] resultData = new String[SIZE];
						resultData[EXP] = tagForExpectedResult;
						resultData[ACT] = tagForActualResult;

						// runtime, max memory usage
						resultData[TIM] = "---";
						resultData[MEM] = "---";
						final String customMessage = fileMsgPair.getValue();
						if (customMessage != null && !customMessage.isEmpty()) {
							// customMessage: expected result, actual result, runtime, max memory usage, original result message
							final String[] message = customMessage.split(" ## ");
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
		
		final StringBuilder sb = new StringBuilder();
		final String lineSeparator = System.getProperty("line.separator");
		
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
		final List<String> files = new ArrayList<String>(fileToLineCount.keySet());
		Collections.sort(files);
		for (final String fileName : files) {
			final String lineCount = fileToLineCount.get(fileName);
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
		
		final Map<String, Map<String, ResultStatistics>> toolResultStatisticsMap = new LinkedHashMap<String, Map<String, ResultStatistics>>();
		toolResultStatisticsMap.put("Abstract Interpretation", wermutResultStatistics);
		toolResultStatisticsMap.put("Automizer", automizerResultStatistics);
		for (final String tool : toolResultStatisticsMap.keySet()) {
			sb.append("\t\\linestrut").append(lineSeparator);
			
			// actual result tag -> result statistics
			final Map<String, ResultStatistics> toolResultStatistics = toolResultStatisticsMap.get(tool);

			final ResultStatistics cummulative = new ResultStatistics();
			for (final ActualResultType a : s_actualResultTypes) {
				final ResultStatistics statistics = toolResultStatistics.get(actualResultTag(a));
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
		final StringBuilder rawData = new StringBuilder();
		for (final ExpectedResultType e : s_expectedResultTypes) {
			final Long[] data = statistics.getData(e);
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
