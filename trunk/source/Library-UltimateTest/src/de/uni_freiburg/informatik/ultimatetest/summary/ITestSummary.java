package de.uni_freiburg.informatik.ultimatetest.summary;

import java.io.File;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;

/**
 * This interface describes test summaries that can be used to create a summary
 * log file of the results of a whole test suite.
 * 
 * As our test suites have typically a lot of tests, it is more convenient to
 * write a summary file to see which test failed why and group the tests
 * according to some criteria. This interface describes classes that can be used
 * to do this.
 * 
 * @author dietsch
 * 
 */
public interface ITestSummary {

	/**
	 * Produces the actual content of the summary.
	 * 
	 * @return A (multi-line) String that will be written to the
	 *         surefire-reports directory of your local Ultimate installation
	 *         with a name specified by {@link #getSummaryLogFileName()}
	 */
	public String getSummaryLog();

	public File getSummaryLogFileName();

	/**
	 * A string that names this test summary 
	 * @return
	 */
	public String getTestSuiteCanonicalName();

	/**
	 * This method is called after the execution of each
	 * {@link UltimateTestCase} and reports the result to the
	 * {@link ITestSummary} instance of the active {@link UltimateTestSuite test
	 * suite}.
	 * 
	 * @param actualResult
	 *            The actual result of the test case.
	 * @param junitResult
	 *            The actual result of the test case mapped to JUnits result
	 *            type
	 * @param category
	 *            The category of this test result as specified by
	 *            {@link ITestResultDecider#getResultCategory()}
	 * @param ultimateRunDefinition
	 *            Input file, settings file and toolchain file.
	 * @param message
	 *            A message for this specific result and this specific input
	 *            file as specified by
	 *            {@link ITestResultDecider#getResultMessage()}
	 * @param ultimateIResults
	 * 	          All IResults produced during the run of Ultimate.
	 *            The results are given as a map which maps plugin IDs to a 
	 *            the list of results produced by that plugin.
	 *            
	 */
	public void addResult(TestResult actualResult, boolean junitResult, 
			String category, UltimateRunDefinition ultimateRunDefinition, 
			String message, Map<String, List<IResult>> ultimateIResults);
}