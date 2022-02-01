package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class OverapproximatingSafetyCheckerOverallResultEvaluator extends SafetyCheckerOverallResultEvaluator {

	@Override
	protected SafetyCheckerOverallResult detectResultCategory(IResult result) {
		if(result instanceof UnprovableResult){
			return SafetyCheckerOverallResult.UNSAFE_OVERAPPROXIMATED;
		}
		return super.detectResultCategory(result);
	}
	
}
