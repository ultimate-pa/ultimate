package de.uni_freiburg.informatik.ultimatetest.decider;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.KeywordBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResult;

/**
 * Use keywords in filename and first line to decide correctness of overflow
 * checks. Since so far we do not use keywords for this we use an empty map.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class SafetyCheckTestResultDecider_Overflow extends SafetyCheckTestResultDecider {

	public SafetyCheckTestResultDecider_Overflow(
			UltimateRunDefinition ultimateRunDefinition,
			boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<SafetyCheckerOverallResult> constructExpectedResultFinder() {
		Map<String, SafetyCheckerOverallResult> emptyMap = Collections.emptyMap();
		return new KeywordBasedExpectedResultFinder<SafetyCheckerOverallResult>(
				emptyMap, null,
				emptyMap);
	}


}
