/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * Use keywords in filename and first line to decide correctness of safety
 * checker results.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class SafetyCheckTestResultDecider extends ThreeTierTestResultDecider<SafetyCheckerOverallResult> {

	/**
	 * 
	 * @param ultimateRunDefinition
	 * 
	 * @param unknownIsJUnitSuccess
	 *            if true the TestResult UNKNOWN is a success for JUnit, if
	 *            false, the TestResult UNKNOWN is a failure for JUnit.
	 */
	public SafetyCheckTestResultDecider(final UltimateRunDefinition ultimateRunDefinition, final boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
		return new KeywordBasedExpectedResultFinder<>(
				TestUtil.constructFilenameKeywordMap_AllSafetyChecker(), null,
				TestUtil.constructFirstlineKeywordMap_SafetyChecker());
	}

	@Override
	public IOverallResultEvaluator<SafetyCheckerOverallResult> constructUltimateResultEvaluation() {
		return new SafetyCheckerOverallResultEvaluator();
	}

	@Override
	public ITestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
		return new SafetyCheckerTestResultEvaluation();
	}

	public class SafetyCheckerTestResultEvaluation implements ITestResultEvaluation<SafetyCheckerOverallResult> {
		private String mCategory;
		private String mMessage;
		private TestResult mTestResult;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				final IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
				compareToOverallResult(expectedResultFinder.getExpectedResult(), overallResultDeterminer);
				return;
			case NO_EXPECTED_RESULT_FOUND:
				evaluateOverallResultWithoutExpectedResult(overallResultDeterminer);
				return;
			default:
				throw new IllegalArgumentException();
			}
		}

		private void evaluateOverallResultWithoutExpectedResult(
				final IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			final SafetyCheckerOverallResult overallResult = overallResultDeterminer.getOverallResult();
			final String overallResultMsg = overallResultDeterminer.generateOverallResultMessage();

			mCategory = overallResult + " (Expected:UNKNOWN)";
			mMessage += " UltimateResult: " + overallResultMsg;
			switch (overallResult) {
			case EXCEPTION_OR_ERROR:
			case UNSUPPORTED_SYNTAX:
			case NO_RESULT:
				mTestResult = TestResult.FAIL;
				break;
			case SAFE:
			case UNSAFE:
			case UNSAFE_DEREF:
			case UNSAFE_FREE:
			case UNSAFE_MEMTRACK:
			case UNSAFE_OVERAPPROXIMATED:
			case UNKNOWN:
			case SYNTAX_ERROR:
			case TIMEOUT:
				mTestResult = TestResult.UNKNOWN;
				break;
			default:
				throw new AssertionError("case not implemented: " + overallResult);
			}
		}

		private void compareToOverallResult(final SafetyCheckerOverallResult expectedResult,
				final IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			final SafetyCheckerOverallResult overallResult = overallResultDeterminer.getOverallResult();
			final String overallResultMsg = overallResultDeterminer.generateOverallResultMessage();

			mCategory = overallResult + " (Expected:" + expectedResult + ")";
			mMessage += " UltimateResult: " + overallResult + "   " + overallResultMsg;
			switch (overallResult) {
			case EXCEPTION_OR_ERROR:
				mCategory = overallResult + " (Expected:" + expectedResult + ") " + overallResultMsg;
				mTestResult = TestResult.FAIL;
				break;
			case SAFE:
				if (expectedResult == SafetyCheckerOverallResult.SAFE) {
					mTestResult = TestResult.SUCCESS;
				} else {
					mTestResult = TestResult.FAIL;
				}
				break;
			case UNSAFE:
			case UNSAFE_DEREF:
			case UNSAFE_FREE:
			case UNSAFE_MEMTRACK:
				if (expectedResult == overallResult) {
					mTestResult = TestResult.SUCCESS;
				} else if (expectedResult == SafetyCheckerOverallResult.UNSAFE) {
					mTestResult = TestResult.SUCCESS;
				} else {
					mTestResult = TestResult.FAIL;
				}
				break;
			case UNSAFE_OVERAPPROXIMATED:
				if (expectedResult == overallResult) {
					mTestResult = TestResult.SUCCESS;
				} else if (expectedResult == SafetyCheckerOverallResult.UNSAFE) {
					mTestResult = TestResult.SUCCESS;
				} else {
					mTestResult = TestResult.UNKNOWN;
				}
				break;
			case UNKNOWN:
				// syntax error should always have been found
				if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
					mTestResult = TestResult.FAIL;
				} else {
					mTestResult = TestResult.UNKNOWN;
				}
				break;
			case SYNTAX_ERROR:
				if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
					mTestResult = TestResult.SUCCESS;
				} else {
					mTestResult = TestResult.FAIL;
				}
				break;
			case TIMEOUT:
				// syntax error should always have been found
				if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
					mTestResult = TestResult.FAIL;
				} else {
					mTestResult = TestResult.UNKNOWN;
				}
				break;
			case UNSUPPORTED_SYNTAX:
				mTestResult = TestResult.FAIL;
				break;
			case NO_RESULT:
				mTestResult = TestResult.FAIL;
				break;
			default:
				throw new AssertionError("case not implemented: " + overallResult);
			}
		}

		private void evaluateExpectedResult(
				final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder) throws AssertionError {
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				mCategory = "Inconsistent keywords";
				mMessage = expectedResultFinder.getExpectedResultFinderMessage();
				mTestResult = TestResult.FAIL;
				break;
			case EXPECTED_RESULT_FOUND:
				mMessage = "ExpectedResult: " + expectedResultFinder.getExpectedResult();
				break;
			case NO_EXPECTED_RESULT_FOUND:
				mMessage = expectedResultFinder.getExpectedResultFinderMessage();
				break;
			default:
				throw new AssertionError(
						"case not implemented: " + expectedResultFinder.getExpectedResultFinderStatus());
			}
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				final Throwable e) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
			case NO_EXPECTED_RESULT_FOUND:
				mCategory += "UltimateResult: " + SafetyCheckerOverallResult.EXCEPTION_OR_ERROR + " " + e.getMessage();
				final ExceptionOrErrorResult res = new ExceptionOrErrorResult("Unknown", e);
				mMessage += " UltimateResult: " + res.getLongDescription();
				return;
			default:
				throw new AssertionError(
						"case not implemented: " + expectedResultFinder.getExpectedResultFinderStatus());
			}
		}

		@Override
		public TestResult getTestResult() {
			return mTestResult;
		}

		@Override
		public String getTestResultCategory() {
			return mCategory;
		}

		@Override
		public String getTestResultMessage() {
			return mMessage;
		}
	}
}
