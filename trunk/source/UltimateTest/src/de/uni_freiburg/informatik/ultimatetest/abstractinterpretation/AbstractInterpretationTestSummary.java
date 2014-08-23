/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.TestSummary;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationTestSummary extends TestSummary {

	/**
	 * @param testSuiteCanonicalName
	 */
	public AbstractInterpretationTestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getFilenameExtension() {
		return ".log";
	}
	
	@Override
	public String getSummaryTypeDescription() {
		return this.getClass().getSimpleName();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary#getSummaryLog()
	 */
	@Override
	public String getSummaryLog() {
		return generateCanonicalSummary().toString();
	}

}
