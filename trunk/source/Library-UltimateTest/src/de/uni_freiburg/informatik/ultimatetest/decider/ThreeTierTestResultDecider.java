package de.uni_freiburg.informatik.ultimatetest.decider;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;

/**
 * Abstract class for deciding a test result in three steps:
 * <ul>
 * <li> 1. Use IExpectedResultFinder to decide expected result for an
 * UltimateRunDefinition
 * <li> 2. Use IResults from Ultimate to decide the overall result provided by
 * Ultimate
 * <li> 3. Compare expected result with the overall result computed by
 * ultimate to decide the test result.
 * </ul> 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT>
 */
public abstract class ThreeTierTestResultDecider<OVERALL_RESULT> implements ITestResultDecider {

	/**
	 * if true the TestResult UNKNOWN is a success for JUnit, if false, 
	 * the TestResult UNKNOWN is a failure for JUnit.
	 */
	private final boolean m_UnknownIsJUnitSuccess;
	private final IExpectedResultFinder<OVERALL_RESULT> m_ExpectedResultEvaluation;
	private IOverallResultEvaluator<OVERALL_RESULT> m_UltimateResultEvaluation;
	private TestResultEvaluation<OVERALL_RESULT> m_TestResultEvaluation;
	
	public ThreeTierTestResultDecider(UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		m_UnknownIsJUnitSuccess = unknownIsJUnitSuccess;
		m_ExpectedResultEvaluation = constructExpectedResultFinder();
		m_ExpectedResultEvaluation.findExpectedResult(ultimateRunDefinition);
	}
	
	@Override
	public final TestResult getTestResult(IResultService resultService) {
		m_UltimateResultEvaluation = constructUltimateResultEvaluation();
		m_UltimateResultEvaluation.evaluateOverallResult(resultService);
		m_TestResultEvaluation = constructTestResultEvaluation();
		m_TestResultEvaluation.evaluateTestResult(m_ExpectedResultEvaluation, m_UltimateResultEvaluation);
		return m_TestResultEvaluation.getTestResult();
	}

	@Override
	public final TestResult getTestResult(IResultService resultService,
			Throwable e) {
		m_TestResultEvaluation = constructTestResultEvaluation();
		m_TestResultEvaluation.evaluateTestResult(m_ExpectedResultEvaluation, e);
		return m_TestResultEvaluation.getTestResult();
	}

	@Override
	public final String getResultMessage() {
		return m_TestResultEvaluation.getTestResultMessage();
	}
	
	@Override
	public final String getResultCategory() {
		return m_TestResultEvaluation.getTestResultCategory();
	}

	@Override
	public boolean getJUnitTestResult(TestResult testResult) {
		switch (testResult) {
		case SUCCESS:
		case UNKNOWN:
			return m_UnknownIsJUnitSuccess;
		case FAIL:
			return false;
		default:
			throw new AssertionError("unknown actualResult");
		}

	}
	
	public abstract IExpectedResultFinder<OVERALL_RESULT> constructExpectedResultFinder();
	
	public abstract IOverallResultEvaluator<OVERALL_RESULT> constructUltimateResultEvaluation();
	
	public abstract TestResultEvaluation<OVERALL_RESULT> constructTestResultEvaluation();
	
	

	public interface TestResultEvaluation<OVERALL_RESULT> {
		public void evaluateTestResult(
				IExpectedResultFinder<OVERALL_RESULT> expectedResultEvaluation,
				IOverallResultEvaluator<OVERALL_RESULT> overallResultDeterminer);
		
		public void evaluateTestResult(IExpectedResultFinder<OVERALL_RESULT> expectedResultEvaluation, Throwable e);
		
		public TestResult getTestResult();
		
		public String getTestResultCategory();
		
		public String getTestResultMessage();
	}
}
