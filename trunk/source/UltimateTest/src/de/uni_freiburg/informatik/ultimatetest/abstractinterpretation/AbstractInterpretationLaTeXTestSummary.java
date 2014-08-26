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
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationLaTeXTestSummary extends TestSummary {

	private final String m_pathOfTrunk;
	
	private final TestResult[] m_testResultTypes = {TestResult.SUCCESS, TestResult.UNKNOWN, TestResult.FAIL};

	// used for determining the table prefix
	private final String m_svcompFolder = "\\examples\\svcomp\\";

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
		return "AbsIntSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		/*
			\begin{longtabu} to \linewidth {cX[l]rccrr}
				\caption{[RESULT WITH CATEGORY]} \\
				\textbf{S} & \textbf{File} & \textbf{LoC} & \textbf{E} & \textbf{A} & \textbf{ms} & \textbf{MiB} \\
				\midrule \midrule
				\sffamily [SOURCE] & \small [FILENAME] & [LINES] & [EXPECTED] & [ACTUAL] & [RUNTIME] & [MAXMEM] \\
			\end{longtabu}
		 */
		
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		Map<TestResult, Integer> count = new HashMap<>();
		
		for (TestResult result : m_testResultTypes) {
			int resultCategoryCount = 0;
			
			String resultTag = getTestResultTag(result);

			for (Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {

				sb.append("\\begin{longtabu} to \\linewidth {cX[l]rccrr}").append(lineSeparator)
					.append("\t\\caption{")
						.append(resultTag)
						.append(", analysis reported ``")
							.append(entry.getKey())
						.append("''")
					.append("} \\\\").append(lineSeparator)
					.append("\t\\textbf{S} & \\textbf{File} & \\textbf{LoC} & \\textbf{E} & \\textbf{A} & \\textbf{ms} & \\textbf{MiB} \\\\").append(lineSeparator)
					.append("\t\\midrule \\midrule \\endhead").append(lineSeparator).append(lineSeparator);
				
				for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
					// \sffamily [SOURCE] & \small [FILENAME] & [LINES] & [EXPECTED] & [ACTUAL] & [RUNTIME] & [MAXMEM] \\
					
					
					// filename and source tag, file size
					String fileName = fileMsgPair.getKey();
					String tablePrefix = "---";
					String fileLines = "---";
					try {
						LineNumberReader reader = new LineNumberReader(new FileReader(new File(fileName)));
						reader.skip(Long.MAX_VALUE);
						fileLines = String.format("%d", reader.getLineNumber());
						reader.close();
					} catch (IOException e) {
						e.printStackTrace();
					}
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
					
					// expected, actual result; runtime, max memory usage
					String customMessage = fileMsgPair.getValue();
					if (customMessage != null && !customMessage.isEmpty()) {
						sb.append(customMessage);
					} else {
						sb.append("--- & --- & --- & --- \\\\");
					}
					sb.append(lineSeparator);
				}

				sb.append("\t\\midrule \\multicolumn{6}{l}{Count} & ").append(entry.getValue().getCount())
					.append(" \\\\ \\midrule \\midrule").append(lineSeparator);

				sb.append("\\end{longtabu}").append(lineSeparator).append(lineSeparator).append(lineSeparator);
				
				resultCategoryCount = resultCategoryCount + entry.getValue().getCount();
			}

			count.put(result, resultCategoryCount);
		}

		sb.append("\\begin{longtabu} to \\linewidth {X[l]r}").append(lineSeparator)
			.append("\t\\caption{Statistics} \\\\").append(lineSeparator)
			.append("\t\\textbf{Result} & \\textbf{Count} \\\\").append(lineSeparator)
			.append("\t\\midrule \\midrule \\endhead").append(lineSeparator);
		int total = 0;
		for (TestResult result : m_testResultTypes) {
			int current = count.get(result);
			sb.append("\t").append(getTestResultTag(result)).append(" & ").append(current).append(" \\\\").append(lineSeparator);
			total += current;
		}
		sb.append("\t\\midrule Total & ").append(total).append(" \\\\ \\midrule \\midrule").append(lineSeparator)
			.append("\\end{longtabu}").append(lineSeparator);
		
		return sb.toString();
	}
	
	private String getTestResultTag(TestResult result) {
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

}
