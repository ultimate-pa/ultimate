package de.uni_freiburg.informatik.ultimate.test.decider;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.SMTLibExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TreeAutomizerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TreeAutomizerOverallResultEvaluator;

public class TreeAutomizerTestResultDecider extends ThreeTierTestResultDecider<TreeAutomizerOverallResult> {

	public TreeAutomizerTestResultDecider(UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public SMTLibExpectedResultFinder<TreeAutomizerOverallResult> constructExpectedResultFinder() {
		return new SMTLibExpectedResultFinder<TreeAutomizerOverallResult>(
				TreeAutomizerOverallResult.UNKNOWN, TreeAutomizerOverallResult.SAT, TreeAutomizerOverallResult.UNSAT);
	}

	@Override
	public TreeAutomizerOverallResultEvaluator constructUltimateResultEvaluation() {
		return new TreeAutomizerOverallResultEvaluator();
	}

	@Override
	public TreeAutomizerTestResultEvaluation constructTestResultEvaluation() {
		return new TreeAutomizerTestResultEvaluation();
	}

	public class TreeAutomizerTestResultEvaluation implements ITestResultEvaluation<TreeAutomizerOverallResult> {

		private TestResult mTestResult;
		private String mCategory;
		private String mMessage;

		@Override
		public void evaluateTestResult(IExpectedResultFinder<TreeAutomizerOverallResult> expectedResultEvaluation,
				IOverallResultEvaluator<TreeAutomizerOverallResult> overallResultDeterminer) {
//			final SMTLibExpectedResultFinder<TreeAutomizerOverallResult> expectedResultFinder = 
//					(SMTLibExpectedResultFinder<TreeAutomizerOverallResult>) expectedResultEvaluation;
//			final TreeAutomizerOverallResultEvaluator overallResultEvaluator = 
//					(TreeAutomizerOverallResultEvaluator) overallResultDeterminer;
			final TreeAutomizerOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();
			final TreeAutomizerOverallResult actualResult = overallResultDeterminer.getOverallResult();
			
			if (expectedResult == TreeAutomizerOverallResult.UNKNOWN) {
				mCategory = "expected result unknown";
				mMessage = "expected: " + expectedResult + " actual: " + actualResult;
				mTestResult = TestResult.UNKNOWN;
			}
			
			if (expectedResult == actualResult) {
				mCategory = "precise match of results (and results are not both UNKOWN..)";
				mMessage = "both results are" + expectedResult;
				mTestResult = TestResult.SUCCESS;
				return;
			}
			
			mCategory = "results don't match";
			mMessage = "expected: " + expectedResult + " actual: " + actualResult;
			mTestResult = TestResult.FAIL;
		}

		@Override
		public void evaluateTestResult(IExpectedResultFinder<TreeAutomizerOverallResult> expectedResultEvaluation,
				Throwable e) {
			final TreeAutomizerOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();

			mCategory = "threw an exception";
			mMessage = "expected: " + expectedResult + " actual: threw an exception";
			mTestResult = TestResult.FAIL;
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
