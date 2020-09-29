package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;

public class VMCAI2021ExampleSuite extends AbstractTraceAbstractionTestSuite {

	private static final String[] SETTINGS = {
			"automizer/concurrent/VMCAI2021_FA.epf",
			"automizer/concurrent/VMCAI2021_PN.epf" };

	private static final String TOOLCHAIN = "AutomizerBplInline.xml";

	private static final String BENCHMARK_FOLDER = "examples/concurrent/bpl/VMCAI2021";

	@Override
	protected ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition) {
		return new SvcompReachTestResultDecider(ultimateRunDefinition, false);
	}

	@Override
	protected long getTimeout() {
		return 300 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : SETTINGS) {
			addTestCase(TOOLCHAIN, setting, new String[] { BENCHMARK_FOLDER }, new String[] { ".bpl" });
		}
		return super.createTestCases();
	}
}
