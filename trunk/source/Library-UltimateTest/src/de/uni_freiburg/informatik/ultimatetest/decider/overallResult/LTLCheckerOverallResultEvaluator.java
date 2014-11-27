package de.uni_freiburg.informatik.ultimatetest.decider.overallResult;

import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.LTLFiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.LTLInfiniteCounterExampleResult;

public class LTLCheckerOverallResultEvaluator extends SafetyCheckerOverallResultEvaluator {

	private int mAllSaveCounter = 0;

	@Override
	protected SafetyCheckerOverallResult detectResultCategory(IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			mAllSaveCounter++;
			if (mAllSaveCounter < 2) {
				return SafetyCheckerOverallResult.NO_RESULT;
			} else {
				return SafetyCheckerOverallResult.SAFE;
			}
		} else if (result instanceof LTLInfiniteCounterExampleResult<?, ?, ?>) {
			return SafetyCheckerOverallResult.UNSAFE;
		} else if (result instanceof LTLFiniteCounterExampleResult<?, ?, ?>) {
			return SafetyCheckerOverallResult.UNSAFE;
		}
		return super.detectResultCategory(result);
	}
}
