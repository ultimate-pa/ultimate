package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * Benchmarks on which we saw the bugs that I reported to Alberto via email on
 * 20221105.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Svcomp23ReachMathsatProblemBenchmarks extends AbstractTraceAbstractionTestSuite {

	private static final int TIMEOUT_IN_SECONDS = 60;

	// @formatter:off
	private static final String[] BENCHMARKS = {
			"examples/svcomp/nla-digbench/freire1.c",
			"examples/svcomp/nla-digbench/freire2.c",
			"examples/svcomp/nla-digbench-scaling/freire1_unwindbound1.c",
			"examples/svcomp/nla-digbench-scaling/freire1_valuebound100.c",
			"examples/svcomp/nla-digbench-scaling/freire2_valuebound1.c",
			"examples/svcomp/nla-digbench-scaling/freire2_unwindbound50.c",
			"examples/svcomp/float-benchs/filter_iir.c",
			"examples/svcomp/float-benchs/inv_sqrt_Quake.c",
			"examples/svcomp/float-newlib/double_req_bl_0530b.c",
			"examples/svcomp/loops/ludcmp.c",
			"examples/svcomp/aws-c-common/aws_hash_table_swap_harness.i",
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
		"default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf",
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
