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
public class Svcomp23ReachSpeedBenchmarks extends AbstractTraceAbstractionTestSuite {

	private static final boolean USE_SAFE_BENCHMARKS = true;
	private static final boolean USE_UNSAFE_BENCHMARKS = true;
	private static final int TIMEOUT_IN_SECONDS = 60;

	// @formatter:off
	private static final String[] BENCHMARKS_UNSAFE_32BIT = {
			"examples/svcomp/array-fpi/s3iff.c",
			"examples/svcomp/array-patterns/array10_pattern.c",
			"examples/svcomp/array-tiling/skippedu.c",
			"examples/svcomp/bitvector-regression/integerpromotion-3.c",
			"examples/svcomp/bitvector/s3_clnt_3.BV.c.cil-2a.c",
			"examples/svcomp/combinations/pc_sfifo_1.cil-1+token_ring.11.cil-2.c",
			"examples/svcomp/eca-rers2012/Problem02_label16.c",
			"examples/svcomp/float-benchs/cast_union_loose.c",
			"examples/svcomp/forester-heap/dll-optional-2.i",
			"examples/svcomp/heap-manipulation/merge_sort-1.i",
			"examples/svcomp/ldv-regression/test27-2.c",
			"examples/svcomp/ldv-sets/test_mutex_double_lock.i",
			"examples/svcomp/list-ext2-properties/simple_and_skiplist_2lvl-1.i",
			"examples/svcomp/list-ext3-properties/sll_length_check-1.i",
			"examples/svcomp/list-properties/alternating_list-2.i",
			"examples/svcomp/locks/test_locks_14-2.c",
			"examples/svcomp/loop-acceleration/underapprox_2-1.c",
			"examples/svcomp/loops/sum01_bug02_sum01_bug02_base.case.i",
			"examples/svcomp/nla-digbench-scaling/egcd2-ll_unwindbound2.c",
			"examples/svcomp/nla-digbench/geo1-u.c",
			"examples/svcomp/openssl-simplified/s3_clnt_1.cil-2.c",
			"examples/svcomp/product-lines/minepump_spec3_product21.cil.c",
			"examples/svcomp/recursive-simple/fibo_2calls_2-1.c",
			"examples/svcomp/recursive/Ackermann02.c",
			"examples/svcomp/reducercommutativity/rangesum.i",
			"examples/svcomp/verifythis/tree_del_iter_incorrect.c",
	};

	private static final String[] BENCHMARKS_SAFE_32BIT = {
			"examples/svcomp/array-examples/data_structures_set_multi_proc_trivial_ground.i",
			"examples/svcomp/aws-c-common/aws_hash_ptr_harness.i",
			"examples/svcomp/bitvector-regression/integerpromotion-2.c",
			"examples/svcomp/bitvector/jain_4-2.c",
			"examples/svcomp/busybox-1.22.0/basename-2.i",
			"examples/svcomp/ddv-machzwd/ddv_machzwd_inb.i",
			"examples/svcomp/eca-rers2012/Problem10_label37.c",
			"examples/svcomp/float-benchs/nan_float_range.c",
			"examples/svcomp/float-newlib/float_req_bl_1010.c",
			"examples/svcomp/floats-cbmc-regression/float11.c",
			"examples/svcomp/floats-esbmc-regression/isgreaterequal.i",
			"examples/svcomp/ldv-commit-tester/m0_drivers-staging-comedi-drivers-ni_pcidio-ko--107_1a--adbbc36.i",
			"examples/svcomp/ldv-linux-3.0/module_get_put-drivers-net-pppox.ko.cil.out.i",
			"examples/svcomp/ldv-linux-3.16-rc1/43_2a_consumption_linux-3.16-rc1.tar.xz-43_2a-drivers--hid--hid-axff.ko-entry_point.cil.out.i",
			"examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_ok_nondet_linux-43_1a-drivers--watchdog--w83877f_wdt.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.i",
			"examples/svcomp/ldv-regression/rule57_ebda_blast.c_1.i",
			"examples/svcomp/locks/test_locks_8.c",
			"examples/svcomp/loop-acceleration/diamond_2-2.c",
			"examples/svcomp/loop-crafted/simple_array_index_value_4.i.v+nlh-reducer.c",
			"examples/svcomp/loop-industry-pattern/ofuf_4.c",
			"examples/svcomp/loop-invariants/even.c",
			"examples/svcomp/loop-invgen/apache-get-tag.i",
			"examples/svcomp/loop-lit/ddlm2013.i",
			"examples/svcomp/loop-new/half.i",
			"examples/svcomp/loop-simple/nested_2.c",
			"examples/svcomp/loop-zilu/benchmark04_conjunctive.i",
			"examples/svcomp/loops-crafted-1/nested5-1.c",
			"examples/svcomp/loops/sum04-2.i",
			"examples/svcomp/nla-digbench-scaling/fermat2-ll_valuebound20.c",
			"examples/svcomp/nla-digbench/geo1-ll.c",
			"examples/svcomp/openssl-simplified/s3_srvr_1a.cil.c",
			"examples/svcomp/product-lines/minepump_spec4_product11.cil.c",
			"examples/svcomp/psyco/psyco_abp_1-3.c",
			"examples/svcomp/recursive-simple/id_b2_o3.c",
			"examples/svcomp/recursive-with-pointer/simple-recursive.c",
			"examples/svcomp/recursive/McCarthy91-2.c",
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
		"default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf",
//		"automizer/interpolation/Reach-32bit-Z3-IcSpLv.epf",
//		"automizer/interpolation/Reach-32bit-CVC4-IcSpLv.epf",
//		"automizer/interpolation/Reach-32bit-CVC5-IcSpLv.epf",
//		"automizer/interpolation/Reach-32bit-MathSAT-IcSpLv.epf",
//		"automizer/interpolation/Reach-32bit-Princess-TreeInterpolation.epf",
//		"automizer/interpolation/Reach-32bit-SMTInterpol-IcSpLv.epf",
//		"automizer/interpolation/Reach-32bit-SMTInterpol-TreeInterpolation.epf",
	};

	private static final String[] TOOLCHAINS = {
		"AutomizerCInline.xml",
		"AutomizerC.xml",
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
