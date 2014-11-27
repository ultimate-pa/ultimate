package de.uni_freiburg.informatik.ultimatetest.decider;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.LTLCheckerOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResult;

public class LTLCheckerTestResultDecider extends SafetyCheckTestResultDecider{

	public LTLCheckerTestResultDecider(UltimateRunDefinition ultimateRunDefinition, boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}
	
	@Override
	public IOverallResultEvaluator<SafetyCheckerOverallResult> constructUltimateResultEvaluation() {
		return new LTLCheckerOverallResultEvaluator();
	}

}
