package de.uni_freiburg.informatik.ultimatetest.decider;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.TerminationAnalysisOverallResult;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.TerminationAnalysisOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * Use keywords in filename and first line to decide correctness of termination
 * analysis result.
 * This class is largely copy and paste from SafetyCheckTestResultDecider.
 * Maybe we can write a good superclass for both.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TerminationAnalysisTestResultDecider extends
		ThreeTierTestResultDecider<TerminationAnalysisOverallResult> {

	public TerminationAnalysisTestResultDecider(
			UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<TerminationAnalysisOverallResult> constructExpectedResultFinder() {
		return new KeywordBasedExpectedResultFinder<TerminationAnalysisOverallResult>(
				Util.constructFilenameKeywordMap_TerminationAnalysis(), 
				null, 
				Util.constructFirstlineKeywordMap_TerminationAnalysis());
	}

	@Override
	public IOverallResultEvaluator<TerminationAnalysisOverallResult> constructUltimateResultEvaluation() {
		return new TerminationAnalysisOverallResultEvaluator();
	}

	@Override
	public ITestResultEvaluation<TerminationAnalysisOverallResult> constructTestResultEvaluation() {
		return new TerminationAnalysisResultEvaluation();
	}
	
	
	
	public class TerminationAnalysisResultEvaluation implements ITestResultEvaluation<TerminationAnalysisOverallResult> {
		String m_Category;
		String m_Message;
		TestResult m_TestResult;

		@Override
		public void evaluateTestResult(
				IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder,
				IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
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
				IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
			m_Category = overallResultDeterminer.getOverallResult() + "(Expected:UNKNOWN)";
			m_Message += " UltimateResult: " + overallResultDeterminer.generateOverallResultMessage();
			switch (overallResultDeterminer.getOverallResult()) {
			case EXCEPTION_OR_ERROR:
			case UNSUPPORTED_SYNTAX:
			case NO_RESULT:
				m_TestResult = TestResult.FAIL;
				break;
			case TERMINATING:
			case NONTERMINATING:
			case UNKNOWN:
			case SYNTAX_ERROR:
			case TIMEOUT:
				m_TestResult = TestResult.UNKNOWN;
				break;
			}
		}

		private void compareToOverallResult(
				TerminationAnalysisOverallResult expectedResult,
				IOverallResultEvaluator<TerminationAnalysisOverallResult> overallResultDeterminer) {
			m_Category = overallResultDeterminer.getOverallResult() + "(Expected:" + expectedResult + ")";
			m_Message += " UltimateResult: " + overallResultDeterminer.getOverallResult() 
					+ "   " + overallResultDeterminer.generateOverallResultMessage();
				switch (overallResultDeterminer.getOverallResult()) {
				case EXCEPTION_OR_ERROR:
					m_TestResult = TestResult.FAIL;
					break;
				case TERMINATING:
					if (expectedResult == TerminationAnalysisOverallResult.TERMINATING) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case NONTERMINATING:
					if (expectedResult == TerminationAnalysisOverallResult.NONTERMINATING) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case UNKNOWN:
					// syntax error should always have been found
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
						m_TestResult = TestResult.FAIL;
					} else {
						m_TestResult = TestResult.UNKNOWN;
					}
					break;
				case SYNTAX_ERROR:
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
						m_TestResult = TestResult.SUCCESS;
					} else {
						m_TestResult = TestResult.FAIL;
					}
					break;
				case TIMEOUT:
					// syntax error should always have been found
					if (expectedResult == TerminationAnalysisOverallResult.SYNTAX_ERROR) {
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
				IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder)
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
				IExpectedResultFinder<TerminationAnalysisOverallResult> expectedResultFinder,
				Throwable e) {
			evaluateExpectedResult(expectedResultFinder);
			switch (expectedResultFinder.getExpectedResultFinderStatus()) {
			case ERROR:
				// we will not evaluate overall result;
				return;
			case EXPECTED_RESULT_FOUND:
			case NO_EXPECTED_RESULT_FOUND:
				m_Category += "/UltimateResult:" + TerminationAnalysisOverallResult.EXCEPTION_OR_ERROR;
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
