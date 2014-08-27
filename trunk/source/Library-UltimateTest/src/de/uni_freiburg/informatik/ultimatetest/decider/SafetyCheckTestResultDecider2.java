package de.uni_freiburg.informatik.ultimatetest.decider;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.ExpectedResultEvaluation;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.KeywordBasedExpectedResultEvaluation;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.util.Util;
import de.uni_freiburg.informatik.ultimatetest.util.Util.ExpectedResult;

public class SafetyCheckTestResultDecider2 extends
		ThreeTierTestResultDecider<SafetyCheckerOverallResult> {

	public SafetyCheckTestResultDecider2(
			UltimateRunDefinition ultimateRunDefinition) {
		super(ultimateRunDefinition);
		// TODO Auto-generated constructor stub
	}

	@Override
	public ExpectedResultEvaluation<SafetyCheckerOverallResult> constructExpectedResultEvaluation() {
		Map<String, SafetyCheckerOverallResult> folderKeywordMap = Collections.emptyMap();
		return new KeywordBasedExpectedResultEvaluation<SafetyCheckerOverallResult>(
				Util.constructFilenameKeywordMap_SafetyChecker(), 
				folderKeywordMap, 
				Util.constructFirstlineKeywordMap_SafetyChecker());
	}

	@Override
	public IOverallResultEvaluator<SafetyCheckerOverallResult> constructUltimateResultEvaluation() {
		return new SafetyCheckerOverallResultEvaluator();
	}

	@Override
	public TestResultEvaluation<SafetyCheckerOverallResult> constructTestResultEvaluation() {
		// TODO Auto-generated method stub
		return null;
	}
	
	
	
	public class SafetyCheckerTestResultEvaluation implements TestResultEvaluation<SafetyCheckerOverallResult> {
		String m_Category;
		String m_Message;
		TestResult m_TestResult;

		@Override
		public void evaluateTestResult(
				ExpectedResultEvaluation<SafetyCheckerOverallResult> expectedResultEvaluation,
				IOverallResultEvaluator<SafetyCheckerOverallResult> overallResultDeterminer) {
			switch (expectedResultEvaluation.getExpectedResultEvaluationStatus()) {
			case ERROR:
				m_Category = "Inkonsistent keywords";
				m_Message = expectedResultEvaluation.getExpectedResultEvaluationMessage();
				m_TestResult = TestResult.FAIL;
				return;
			case DETERMINED:

			case UNKNOWN:
				
			default:
				throw new AssertionError("unknown case");
			}
		}

		@Override
		public void evaluateTestResult(
				ExpectedResultEvaluation<SafetyCheckerOverallResult> expectedResultEvaluation,
				Throwable e) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public TestResult getTestResult() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String getTestResultCategory() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String getTestResultMessage() {
			// TODO Auto-generated method stub
			return null;
		}
		
	}

}
