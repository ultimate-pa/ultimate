package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Svcomp23ConcurrencySpeedBenchmarks extends AbstractTraceAbstractionTestSuite {

	private static final boolean USE_SAFE_BENCHMARKS = true;
	private static final boolean USE_UNSAFE_BENCHMARKS = true;
	private static final int TIMEOUT_IN_SECONDS = 120;

	// @formatter:off
	private static final String[] BENCHMARKS_UNSAFE_32BIT_OLD = {
			"examples/svcomp/goblint-regression/13-privatized_19-publish-precision_unknown_1_pos.i",
			"examples/svcomp/ldv-races/race-2_3-container_of.i",
			"examples/svcomp/pthread-atomic/qrcu-2.i",
			"examples/svcomp/pthread-lit/fkp2013_variant-2.i",
			"examples/svcomp/pthread-wmm/rfi005.i",
			"examples/svcomp/pthread/lazy01.i",
	};

	private static final String[] BENCHMARKS_SAFE_32BIT_OLD = {
			"examples/svcomp/goblint-regression/13-privatized_45-traces-per-global-and-current-lock-mine-incomparable_true.i",
			"examples/svcomp/ldv-races/race-1_1-join.i",
			"examples/svcomp/pthread-atomic/dekker.i",
			"examples/svcomp/pthread-divine/condvar.i",
			"examples/svcomp/pthread-ext/17_szymanski.i",
			"examples/svcomp/pthread-lit/qw2004-1.i",
			"examples/svcomp/pthread-wmm/safe020_pso.oepc_pso.opt_tso.oepc_tso.opt.i",
			"examples/svcomp/pthread/singleton_with-uninit-problems.i",
			"examples/svcomp/weaver/parallel-bluetooth.wvr.c",
	};

	private static final String[] BENCHMARKS_UNSAFE_32BIT = {
			"examples/svcomp/goblint-regression/13-privatized_19-publish-precision_unknown_1_pos.i",
			"examples/svcomp/ldv-races/race-2_3-container_of.i",
			"examples/svcomp/pthread-atomic/qrcu-2.i",
			"examples/svcomp/pthread-lit/fkp2013_variant-2.i",
			"examples/svcomp/pthread-wmm/rfi005.i",
			"examples/svcomp/pthread/lazy01.i",

			"examples/svcomp/ldv-races/race-2_2-container_of.i",
			"examples/svcomp/pthread-wmm/mix017.oepc.i",
			"examples/svcomp/pthread/stack_longer-1.i",
	};

	private static final String[] BENCHMARKS_SAFE_32BIT = {
			"examples/svcomp/goblint-regression/13-privatized_45-traces-per-global-and-current-lock-mine-incomparable_true.i",
			"examples/svcomp/ldv-races/race-1_1-join.i",
			"examples/svcomp/pthread-atomic/dekker.i",
			"examples/svcomp/pthread-divine/condvar.i",
			"examples/svcomp/pthread-ext/17_szymanski.i",
			"examples/svcomp/pthread-lit/qw2004-1.i",
			"examples/svcomp/pthread-wmm/safe020_pso.oepc_pso.opt_tso.oepc_tso.opt.i",
			"examples/svcomp/pthread/singleton_with-uninit-problems.i",
			"examples/svcomp/weaver/parallel-bluetooth.wvr.c",

			"examples/svcomp/goblint-regression/36-apron_21-traces-cluster-based_true.i",
			"examples/svcomp/pthread-atomic/read_write_lock-1.i",
			"examples/svcomp/pthread-wmm/safe035_power.i",
			"examples/svcomp/pthread/triangular-longer-1.i",
			"examples/svcomp/weaver/chl-collitem-subst.wvr.c",
	};

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompTestResultDeciderUnreachCall(urd, false);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return TIMEOUT_IN_SECONDS * 1000;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS_32BIT = {
		"default/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-VariableLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-VariableLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Dbo.epf",
	};

	private static final String[] TOOLCHAINS = {
		"AutomizerCInline.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (USE_SAFE_BENCHMARKS) {
			for (final String file : BENCHMARKS_SAFE_32BIT) {
				for (final String setting : SETTINGS_32BIT) {
					for (final String toolchain : TOOLCHAINS) {
						addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(file, setting, toolchain,
								getTimeout()));
					}
				}
			}
		}
		if (USE_UNSAFE_BENCHMARKS) {
			for (final String file : BENCHMARKS_UNSAFE_32BIT) {
				for (final String setting : SETTINGS_32BIT) {
					for (final String toolchain : TOOLCHAINS) {
						addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(file, setting, toolchain,
								getTimeout()));
					}
				}
			}
		}
		return super.createTestCases();
	}

}
