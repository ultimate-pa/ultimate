package de.uni_freiburg.informatik.ultimatetest.decider;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

/**
 * A TestResultDecider is responsible for translating from the expected result
 * of the test and the actual result of Ultimate to {@link TestResult test
 * results} that in turn will be used to set the JUnit test result.
 * 
 * {@link UltimateTestCase} will call the methods of this interface <b>after
 * each test case run</b> and determine the JUnit result based on their return
 * values and the implementation of {@link #getJUnitSuccess(TestResult)}.
 * 
 * @author dietsch
 * 
 */
public interface ITestResultDecider {

	/**
	 * If the execution of an {@link UltimateTestCase} does not generate a
	 * {@link Throwable}, this method will be called by {@link UltimateTestCase}
	 * to determine the actual test result.
	 * 
	 * @param resultService
	 *            Provides the {@link IUltimateServiceProvider} instance of the
	 *            toolchain that was run for the test on which
	 *            {@link ITestResultDecider} should decide.
	 */
	public TestResult getTestResult(IResultService resultService);

	/**
	 * If the execution of an {@link UltimateTestCase} does generate a
	 * {@link Throwable}, this method will be called by {@link UltimateTestCase}
	 * to determine the actual test result.
	 * 
	 * @param resultService
	 *            Provides the {@link IUltimateServiceProvider} instance of the
	 *            toolchain that was run for the test on which
	 *            {@link ITestResultDecider} should decide.
	 * 
	 * @param e
	 *            The {@link Throwable} that caused Ultimate to end its
	 *            execution.
	 */
	public TestResult getTestResult(IResultService resultService, Throwable e);

	/**
	 * After {@link UltimateTestCase} called {@link #getTestResult()} or
	 * {@link #getTestResult(IResultService)}, {@link UltimateTestCase} may call this
	 * method to retrieve a custom message for potentially active ITestSummary
	 * classes.
	 * 
	 * The message should be used by {@link ITestSummary} to report individual
	 * informations for a given input file and a given result.
	 * 
	 * @return A String representing the result message. May be null.
	 */
	public String getResultMessage();

	/**
	 * After {@link UltimateTestCase} called {@link #getTestResult()} or
	 * {@link #getTestResult(IResultService)}, {@link UltimateTestCase} may call this
	 * method to retrieve a custom category for potentially active ITestSummary
	 * classes.
	 * 
	 * The category should be used by {@link ITestSummary} to group tests of a
	 * test suite.
	 * 
	 * The category string is not necessarily related to the result computed by
	 * Ultimate, nor related to the expected result. It can be chosen freely by
	 * the {@link ITestResultDecider} implementer.
	 * 
	 * @return A String representing the result category. May be null.
	 */
	public String getResultCategory();

	/**
	 * This method should provide a mapping from {@link TestResult} to the
	 * actual JUnitTest result.
	 * 
	 * @param actualResult
	 *            The result obtained from {@link #getTestResult()} or
	 *            {@link #isResultFail(Throwable))} of this instance.
	 * @return true iff the JUnitTest should pass, fail iff it should fail.
	 */
	public boolean getJUnitSuccess(TestResult actualResult);

	/**
	 * This enum represents the actual results of a test.
	 * 
	 * @author dietsch
	 */
	public enum TestResult {
		/**
		 * Fail should always represent a JUnit test failure.
		 */
		FAIL,
		/**
		 * Unknown has to be interpreted by
		 * {@link ITestResultDecider#getJUnitTestResult(TestResult)} and may be
		 * mapped to a JUnit test failure or a JUnit test success.
		 */
		UNKNOWN,
		/**
		 * Success should always represent a JUnit test success.
		 */
		SUCCESS
	}

}
