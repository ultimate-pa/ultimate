/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationTestSummary extends TestSummary {

	private final String m_logFileName;
	
	/**
	 * @param testSuiteCanonicalName
	 */
	public AbstractInterpretationTestSummary(String testSuiteCanonicalName, String logFileName) {
		super(testSuiteCanonicalName);
		m_logFileName = logFileName;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		return generateCanonicalSummary().toString();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLogFileName()
	 */
	@Override
	public File getSummaryLogFileName() {
		return new File(m_logFileName);
	}

}
