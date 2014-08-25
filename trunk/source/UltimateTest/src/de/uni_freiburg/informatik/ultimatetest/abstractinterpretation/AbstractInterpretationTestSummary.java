/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

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
public class AbstractInterpretationTestSummary extends TestSummary {

	private final String m_pathOfTrunk;
	
	private final TestResult[] m_testResultTypes = {TestResult.SUCCESS, TestResult.UNKNOWN, TestResult.FAIL};

	private final boolean m_logAsLaTeXTable;
	
	// used for determining the table prefix if m_logAsLaTeXTable
	private final String m_ultimateFolder = "\\examples\\";
	private final String m_svcompFolder = "\\svcomp\\";
	
	/**
	 * @param testSuiteCanonicalName
	 */
	public AbstractInterpretationTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			boolean logAsLaTeXTable) {
		super(ultimateTestSuite);
		m_logAsLaTeXTable = logAsLaTeXTable;
		
		m_pathOfTrunk = Util.getPathFromTrunk("");
	}
	
	@Override
	public String getFilenameExtension() {
		return m_logAsLaTeXTable ? ".tex" : ".log";
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return m_logAsLaTeXTable ? "AbsIntLaTeXSummary" : "AbsIntLogSummary";
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		if (m_logAsLaTeXTable) {
			StringBuilder sb = new StringBuilder();
			String lineSeparator = System.getProperty("line.separator");
			Map<TestResult, Integer> count = new HashMap<>();
	
			sb.append("\\begin{longtable}{lXr}").append(lineSeparator)
				.append("\t\\hline \\hline \\endfirsthead").append(lineSeparator)
				.append("\t\\hline \\endhead").append(lineSeparator);
			
			for (TestResult result : m_testResultTypes) {
				int resultCategoryCount = 0;
				
				String resultTag = getTestResultTag(result);
	
				for (Entry<String, Summary> entry : getSummaryMap(result).entrySet()) {
					
					sb.append("\t\\multicolumn{3}{c}{\\bfseries ").append(resultTag)
						.append(", analysis reported ``").append(entry.getKey()).append("''} \\\\ \\hline").append(lineSeparator);
					
					for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage().entrySet()) {
						
						String fileName = fileMsgPair.getKey().replace(m_pathOfTrunk, "");
						String tablePrefix = "";
						if (fileName.startsWith(m_ultimateFolder)) {
							fileName = fileName.substring(m_ultimateFolder.length());
							tablePrefix = "U";
						} else if (fileName.startsWith(m_svcompFolder)) {
							fileName = fileName.substring(m_svcompFolder.length());
							tablePrefix = "S";
						}
						fileName = fileName.replace("\\", "\\textbackslash ");
						
						sb.append("\t\t\\sffamily ").append(tablePrefix).append(" & \\sffamily\\small ").append(fileName).append(" & ");
						String customMessage = fileMsgPair.getValue();
						if (customMessage != null && !customMessage.isEmpty()) {
							sb.append(customMessage);
						} else {
							sb.append("$\\emptyset$");
						}
						sb.append(" \\\\").append(lineSeparator);
					}
	
					sb.append("\t\t\\hline \\multicolumn{2}{l}{Count} & ").append(entry.getValue().getCount()).append(" \\\\ \\hline \\hline").append(lineSeparator);
					
					resultCategoryCount = resultCategoryCount + entry.getValue().getCount();
				}
	
				count.put(result, resultCategoryCount);
			}
	
			sb.append("\t\\multicolumn{3}{c}{\\bfseries Statistics} \\\\ \\hline").append(lineSeparator);
			int total = 0;
			for (TestResult result : m_testResultTypes) {
				int current = count.get(result);
				sb.append("\t\t \\multicolumn{2}{l}{").append(getTestResultTag(result)).append("} & ").append(current).append(" \\\\").append(lineSeparator);
				total += current;
			}
			sb.append("\t\t\\hline \\multicolumn{2}{l}{Total} &").append(total).append(" \\\\ \\hline \\hline").append(lineSeparator);
	
			sb.append("\\end{longtable}").append(lineSeparator);
			
			return sb.toString();
		}

		// no LaTeX
		return super.generateCanonicalSummary().toString();
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
