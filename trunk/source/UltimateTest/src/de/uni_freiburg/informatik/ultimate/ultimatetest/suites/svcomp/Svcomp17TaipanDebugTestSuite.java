/*
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.svcomp;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class Svcomp17TaipanDebugTestSuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	protected long getTimeout() {
		// Time for each test in milliseconds.

		// return -1;
		return 90 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (int i = 0; i < TESTCASES.length; i++) {
			@SuppressWarnings("unchecked")
			final Triple<String, String, String> triple = (Triple<String, String, String>) TESTCASES[i];
			final String toolchain = triple.getFirst();
			final String settings = triple.getSecond();
			final String file = triple.getThird();

			addTestCase(toolchain, settings, file);
		}
		return super.createTestCases();
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Avg. runtime", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallIterations.toString(), "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntIterations.toString(), "AI Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntStrong.toString(), "AI Strong",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntTime.toString(), "AI Avg. Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Trace Abstraction Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantCoveringCapability", "ICC", ConversionContext.Percent(true, 2),
						Aggregate.Ignore, Aggregate.Average), };
	}

	// Mapping:
	// AutomizerCInline_WitnessPrinter.xml -> TaipanReach.xml
	// TaipanMemDerefMemtrack.xml -> AutomizerCInline_WitnessPrinter.xml

	// @formatter:off
	private static final Object[] TESTCASES = {
			// Differences between utaipan and uautomizer
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-ControlFlow.xml.bz2.merged.xml

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Arrays.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--hwmon--nct6775.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--u132-hcd.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/avg05_true-unreach-call.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/avg10_true-unreach-call.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/sum05_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/sum10_true-unreach-call.i"),

			// ****** utaipan: "unknown", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/rangesum60_false-unreach-call.i"),

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "true" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_malloc_ex9_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc2_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strlen_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/selectionSort_recursive_true-termination.c.i

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--virtio_blk.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--xen-blkfront.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--input--touchscreen--usbtouchscreen.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--misc--sgi-gru--gru.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--can--janz-ican3.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--ethernet--smsc--smc91c92_cs.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--scsi--megaraid.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--isp116x-hcd.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Heap.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-queue_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-buckets_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-queue_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-sorted_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext2-properties/list_and_tree_cnstr_false-unreach-call.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "unknown" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-BitVectors.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_1_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_2_alt_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_2_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_3_alt_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_3_true-unreach-call_true-no-overflow.BV.c.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "unknown" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_1652.results.sv-comp17.Overflows-BitVectors.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.UNBOUNDED.pals.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.UNBOUNDED.pals.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "TIMEOUT" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-numeric/recHanoi02_true-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-numeric/rec_counter1_true-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-numeric/rec_counter3_true-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-numeric/twisted_true-termination_true-no-overflow.c

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1651.results.sv-comp17.ConcurrencySafety-Main.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.UNBOUNDED.pals.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.UNBOUNDED.pals.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "unknown" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: pthread-atomic/gcd_true-unreach-call_true-termination.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: pthread-atomic/gcd_true-unreach-call_true-termination.i

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Loops.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loops/eureka_05_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loops/matrix_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loop-acceleration/diamond_true-unreach-call1_true-termination.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loops/s3_false-unreach-call.i"),
			// End of multiple calls of utaipan


			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-Arrays.xml.bz2.merged.xml

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-memsafety/memleaks_test13_true-valid-memsafety.i"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/array-memsafety/lis-alloca_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_1736.results.sv-comp17.Termination-MainControlFlow.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_15_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_10_true-unreach-call.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan


			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-LinkedLists.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "unknown" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-simple-white-blue_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-simple-white-blue_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/list_flag_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/list_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/simple_built_from_end_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/simple_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/splice_true-unreach-call_false-valid-memtrack.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "false(valid-deref)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-01_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1736.results.sv-comp17.Termination-MainHeap.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "true" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_malloc_ex9_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc2_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strlen_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/selectionSort_recursive_true-termination.c.i

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-ECA.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label00_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label08_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label09_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label13_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label14_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label19_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label25_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label27_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label31_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label34_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label39_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label40_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label41_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label46_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label51_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label52_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem01_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label00_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label08_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label09_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label12_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label14_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label15_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label25_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label31_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label35_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label37_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label38_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label39_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label40_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label41_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label52_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label54_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem02_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label08_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label14_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label32_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label38_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label40_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label57_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem03_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label00_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label08_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label20_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label25_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label34_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label37_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label41_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label44_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label46_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label50_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label51_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label54_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label57_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem04_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem05_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem05_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label00_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label08_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label09_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label13_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label14_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label27_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label39_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label44_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label51_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label52_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label54_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem10_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label09_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label13_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label27_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label32_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label37_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label38_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label52_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label57_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem11_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label12_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label14_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label15_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label27_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label31_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label41_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label44_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label46_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem12_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem13_label20_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label01_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label03_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label15_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label19_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label20_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label25_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label32_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label33_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label38_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label50_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem14_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label04_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label06_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label31_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label35_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label44_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label46_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label54_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label57_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem15_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label09_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label12_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label13_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label19_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label24_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label25_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label26_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label29_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label32_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label34_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label35_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label36_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label39_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label40_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label45_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label49_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label50_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label55_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label57_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem16_label59_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem17_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem17_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label02_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label05_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label07_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label11_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label13_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label16_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label17_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label18_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label21_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label22_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label23_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label28_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label30_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label40_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label41_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label42_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label43_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label44_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label46_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label47_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label48_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label50_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label51_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label53_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label54_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label56_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label58_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/eca-rers2012/Problem18_label59_true-unreach-call.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "false(valid-deref)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-01_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),

			// ****** utaipan: "ERROR (1)", uautomizer: "false(termination)" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-restricted-15/TwoFloatInterv_false-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-restricted-15/UpAndDownIneq_false-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-restricted-15/UpAndDown_false-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-restricted-15/WhilePart_false-termination_true-no-overflow.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-restricted-15/WhileSingle_false-termination_true-no-overflow.c

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1652.results.sv-comp17.Overflows-Other.xml.bz2.merged.xml

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/MultCommutative_true-unreach-call_true-no-overflow_true-termination.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-Other.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "ERROR" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/ls-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/seq_true-no-overflow_true-valid-memsafety.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.Systems_BusyBox_MemSafety.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "ERROR" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/basename_false-unreach-call_true-no-overflow_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/basename_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/basename_false-unreach-call_true-no-overflow_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/basename_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loops/s3_false-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "ERROR" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/ls-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			             "examples/svcomp/busybox-1.22.0/seq_true-no-overflow_true-valid-memsafety.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1736.results.sv-comp17.Termination-Other.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition01_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition02_false-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition03_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/EvenOdd01_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/EvenOdd03_false-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/recHanoi02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/recHanoi03_true-unreach-call_true-no-overflow_true-termination.c"),

			// ****** utaipan: "unknown", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "TIMEOUT" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: seq-mthreaded/rekh_ctm_true-unreach-call.3_true-termination.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: seq-mthreaded/rekh_ctm_true-unreach-call.4_true-termination.c

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.Systems_DeviceDriversLinux64_ReachSafety.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--hwmon--nct6775.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--u132-hcd.ko_true-unreach-call.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__linux-kernel-locking-mutex__drivers-net-wireless-libertas-libertas_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--hid--hid-wiimote.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--media--usb--ttusb-budget--dvb-ttusb-budget.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--class--cdc-wdm.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--gadget--udc--net2272.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--gadget--udc--pch_udc.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--misc--iowarrior.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--misc--uss720.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--misc--yurex.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--video--fbdev--s3fb.ko_false-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--vme--bridges--vme_ca91cx42.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--xen--xen-pciback--xen-pciback.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---fs--squashfs--squashfs.ko_true-unreach-call.cil.c"),

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "true" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_malloc_ex9_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc2_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strcopy_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/rec_strlen_malloc_true-termination.c.i
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: termination-recursive-malloc/selectionSort_recursive_true-termination.c.i

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--virtio_blk.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--xen-blkfront.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--input--touchscreen--usbtouchscreen.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--misc--sgi-gru--gru.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--can--janz-ican3.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--ethernet--smsc--smc91c92_cs.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--scsi--megaraid.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--isp116x-hcd.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1652.results.sv-comp17.Systems_BusyBox_Overflows.xml.bz2.merged.xml

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Recursive.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_10_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_15_true-unreach-call.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_10_true-unreach-call.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/MultCommutative_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/MultCommutative_true-unreach-call_true-no-overflow_true-termination.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Floats.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition01_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition02_false-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Addition03_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/EvenOdd01_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/EvenOdd03_false-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/recHanoi02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/recHanoi03_true-unreach-call_true-no-overflow_true-termination.c"),

			// ****** utaipan: "unknown", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "ERROR (1)", uautomizer: "TIMEOUT" ******
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: seq-mthreaded/rekh_ctm_true-unreach-call.3_true-termination.c
			// *** No suitable toolchain file found using *Termination.xml
			// *** File: seq-mthreaded/rekh_ctm_true-unreach-call.4_true-termination.c

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-ProductLines.xml.bz2.merged.xml

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product01_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product02_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product09_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product10_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product38_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product40_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product45_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product46_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product47_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product48_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product53_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product54_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product55_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product59_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product60_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product61_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product62_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product63_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec2_product64_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product37_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product45_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product46_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product53_true-unreach-call_false-termination.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/minepump_spec3_product54_true-unreach-call_false-termination.cil.c"),
			// End of multiple calls of utaipan
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product57_true-unreach-call_false-termination.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/product-lines/minepump_spec3_product61_true-unreach-call_false-termination.cil.c"),

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Sequentialized.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.UNBOUNDED.pals.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.UNBOUNDED.pals.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-Heap.xml.bz2.merged.xml

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-memsafety/memleaks_test13_true-valid-memsafety.i"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			                "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerCInline_WitnessPrinter.xml",
			             "default/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),

	};
	// @formatter:on
}
