/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.decider;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;

/**
 * A TestResultDecider is responsible for translating from the expected result
 * of the test and the actual result of Ultimate to {@link TestResult test
 * results} that in turn will be used to set the JUnit test result.
 * {@link UltimateTestCase} will call the methods of this interface <b>after
 * each test case run</b> and determine the JUnit result based on their return
 * values and the implementation of {@link #getJUnitSuccess(TestResult)}.
 * 
 * @author dietsch
 */
public interface ITestResultDecider {
	/**
	 * If the execution of an {@link UltimateTestCase} does not generate a
	 * {@link Throwable}, this method will be called by {@link UltimateTestCase}
	 * to determine the actual test result.
	 * 
	 * @param services
	 *            Provides the {@link IUltimateServiceProvider} instance of the
	 *            toolchain that was run for the test on which
	 *            {@link ITestResultDecider} should decide.
	 */
	public TestResult getTestResult(IUltimateServiceProvider services);
	
	/**
	 * If the execution of an {@link UltimateTestCase} does generate a
	 * {@link Throwable}, this method will be called by {@link UltimateTestCase}
	 * to determine the actual test result.
	 * 
	 * @param services
	 *            Provides the {@link IUltimateServiceProvider} instance of the
	 *            toolchain that was run for the test on which
	 *            {@link ITestResultDecider} should decide.
	 * @param e
	 *            The {@link Throwable} that caused Ultimate to end its
	 *            execution.
	 */
	public TestResult getTestResult(IUltimateServiceProvider services, Throwable e);
	
	/**
	 * After {@link UltimateTestCase} called {@link #getTestResult()} or
	 * {@link #getTestResult(de.uni_freiburg.informatik.ultimate.core.model.services.IResultService)},
	 * {@link UltimateTestCase} may call this
	 * method to retrieve a custom message for potentially active ITestSummary
	 * classes.
	 * The message should be used by {@link ITestSummary} to report individual
	 * informations for a given input file and a given result.
	 * 
	 * @return A String representing the result message. May be null.
	 */
	public String getResultMessage();
	
	/**
	 * After {@link UltimateTestCase} called {@link #getTestResult()} or
	 * {@link #getTestResult(de.uni_freiburg.informatik.ultimate.core.model.services.IResultService)},
	 * {@link UltimateTestCase} may call this
	 * method to retrieve a custom category for potentially active ITestSummary
	 * classes.
	 * The category should be used by {@link ITestSummary} to group tests of a
	 * test suite.
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
