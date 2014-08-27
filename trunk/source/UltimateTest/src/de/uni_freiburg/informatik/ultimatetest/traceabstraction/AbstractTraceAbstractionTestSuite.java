package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import de.uni_freiburg.informatik.ultimatetest.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider2;

public abstract class AbstractTraceAbstractionTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(
			UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider2(ultimateRunDefinition, true);
	}

}
