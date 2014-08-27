package de.uni_freiburg.informatik.ultimatetest.decider;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Use keywords in filename and first line to decide correctness of safety
 * checker results.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class SafetyCheckTestResultDecider2 extends
		ThreeTierTestResultDecider<SafetyCheckerOverallResult> {

	public SafetyCheckTestResultDecider2(
			UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
		return new KeywordBasedExpectedResultFinder<SafetyCheckerOverallResult>(
				Util.constructFilenameKeywordMap_SafetyChecker(), 
				null, 
				Util.constructFirstlineKeywordMap_SafetyChecker());
	}

	@Override
	public IOverallResultEvaluator<SafetyCheckerOverallResult> constructUltimateResultEvaluation() {
		return new SafetyCheckerOverallResultEvaluator();
	}

	@Override
	public TestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
		return new SafetyCheckerTestResultEvaluation();
	}
	
	
	
	public class SafetyCheckerTestResultEvaluation implements TestResultEvaluation<SafetyCheckerOverallResult> {
		String m_Category;
		String m_Message;
		TestResult m_TestResult;

		@Override
		public void evaluateTestResult(
				IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
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
			}
		}
		
		private void evaluateOverallResultWithoutExpectedResult(
				IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			m_Category = overallResultDeterminer.getOverallResult() + "(Expected:UNKNOWN)";
			m_Message += " UltimateResult: " + overallResultDeterminer.generateOverallResultMessage();
			switch (overallResultDeterminer.getOverallResult()) {
			case EXCEPTION_OR_ERROR:
			case UNSUPPORTED_SYNTAX:
			case NO_RESULT:
				m_TestResult = TestResult.FAIL;
				break;
			case SAFE:
			case UNSAFE:
			case UNKNOWN:
			case SYNTAX_ERROR:
			case TIMEOUT:
				m_TestResult = TestResult.UNKNOWN;
				break;
			}
		}

		private void compareToOverallResult(
				SafetyCheckerOverallResult expectedResult,
				IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			m_Category = overallResultDeterminer.getOverallResult() + "(Expected:" + expectedResult + ")";
			m_Message += " UltimateResult: " + overallResultDeterminer.getOverallResult() 
					+ "   " + overallResultDeterminer.generateOverallResultMessage();
				switch (overallResultDeterminer.getOverallResult()) {
				case EXCEPTION_OR_ERROR:
					m_TestResult = TestResult.FAIL;
					break;
				case SAFE:
					if (expectedResult == SafetyCheckerOverallResult.SAFE) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case UNSAFE:
					if (expectedResult == SafetyCheckerOverallResult.UNSAFE) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case UNKNOWN:
					// syntax error should always have been found
					if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
						m_TestResult = TestResult.FAIL;
					} else {
						m_TestResult = TestResult.UNKNOWN;
					}
					break;
				case SYNTAX_ERROR:
					if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case TIMEOUT:
					// syntax error should always have been found
					if (expectedResult == SafetyCheckerOverallResult.SYNTAX_ERROR) {
						m_TestResult = TestResult.FAIL;
					} else {
						m_TestResult = TestResult.UNKNOWN;
					}
					break;
				case UNSUPPORTED_SYNTAX:
					m_TestResult = TestResult.FAIL;
					break;
				case NO_RESULT:
					m_TestResult = TestResult.FAIL;
					break;
				default:
					throw new AssertionError("unknown case");
				}
		}

		private void evaluateExpectedResult(
				IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder)
				throws AssertionError {
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				m_Category = "Inkonsistent keywords";
				m_Message = expectedResultFinder.getExpectedResultFinderMessage();
				m_TestResult = TestResult.FAIL;
				break;
			case EXPECTED_RESULT_FOUND:
				m_Message = "ExpectedResult: " + expectedResultFinder.getExpectedResult();
				break;
			case NO_EXPECTED_RESULT_FOUND:
				m_Message = expectedResultFinder.getExpectedResultFinderMessage();
				break;
			default:
				throw new AssertionError("unknown case");
			}
		}

		@Override
		public void evaluateTestResult(
				IExpectedResultFinder<SafetyCheckerOverallResult> expectedResultFinder,
				Throwable e) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
			case NO_EXPECTED_RESULT_FOUND:
				m_Category += "/UltimateResult:" + SafetyCheckerOverallResult.EXCEPTION_OR_ERROR;
				m_Message += " UltimateResult: " + e.getMessage();
			default:
				break;
			}
		}

		@Override
		public TestResult getTestResult() {
			return m_TestResult;
		}

		@Override
		public String getTestResultCategory() {
			return m_Category;
		}

		@Override
		public String getTestResultMessage() {
			return m_Message;
		}
		
	}

}
