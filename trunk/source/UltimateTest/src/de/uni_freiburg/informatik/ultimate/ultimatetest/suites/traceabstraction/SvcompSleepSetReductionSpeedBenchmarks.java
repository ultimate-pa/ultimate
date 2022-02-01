package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class SvcompSleepSetReductionSpeedBenchmarks extends AbstractTraceAbstractionTestSuite {
	private static final int TIMEOUT = 1000; // seconds

	// @formatter:off
	private static final String[] BENCHMARKS = {
			"examples/svcomp/pthread-atomic/szymanski.i",
			"examples/svcomp/pthread-wmm/safe000_tso.oepc.i",
			"examples/svcomp/pthread-wmm/safe004_tso.opt.i",
			"examples/svcomp/pthread-wmm/rfi001_power.opt.i",
			"examples/svcomp/pthread-wmm/rfi001_tso.opt.i",
			"examples/svcomp/pthread-wmm/mix041_tso.oepc.i",
			"examples/svcomp/pthread-wmm/safe005_pso.opt.i",
			"examples/svcomp/pthread-wmm/thin000_power.opt.i",
			"examples/svcomp/pthread-wmm/safe006_power.opt.i",
			"examples/svcomp/pthread-wmm/safe018_power.opt.i",
			"examples/svcomp/pthread-wmm/safe028_power.opt.i",
			"examples/svcomp/pthread-wmm/safe028_power.oepc.i",
			"examples/svcomp/pthread-wmm/thin001_power.opt.i",
			"examples/svcomp/pthread-wmm/thin002_tso.opt.i",
			"examples/svcomp/pthread-wmm/safe035_power.oepc.i",
			"examples/svcomp/pthread-wmm/mix055_pso.opt.i",
			"examples/svcomp/pthread-wmm/safe035_power.opt.i",
			"examples/svcomp/pthread-wmm/mix044_power.opt.i",
			"examples/svcomp/pthread-wmm/safe019_power.opt.i",
			"examples/svcomp/pthread-wmm/mix029_power.opt.i",
			"examples/svcomp/pthread-wmm/mix047_pso.opt.i",
			"examples/svcomp/pthread-wmm/mix040_tso.opt.i",
			"examples/svcomp/pthread-wmm/mix030_power.opt.i",

			"examples/svcomp/pthread-wmm/safe005_power.opt.i",
			"examples/svcomp/pthread-wmm/safe005_rmo.oepc.i",
			"examples/svcomp/pthread-wmm/safe005_rmo.opt.i",

			// TODO has other (Z3?) problems; debug later
			//"examples/svcomp/pthread/triangular-longer-1.i"
	};


	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompReachTestResultDecider(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return TIMEOUT * 1000L;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS_32BIT = {
		//"default/automizer/svcomp-Reach-32bit-Automizer_Default.epf"
		//"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-Sleep-NoLbe-Delay.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-Sleep-NoLbe-New_States.epf"
	};

	private static final String[] TOOLCHAINS = {
		"AutomizerCInline.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String file : BENCHMARKS) {
			for (final String setting : SETTINGS_32BIT) {
				for (final String toolchain : TOOLCHAINS) {
					addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(file, setting, toolchain,
							getTimeout()));
				}
			}
		}
		return super.createTestCases();
	}

}
