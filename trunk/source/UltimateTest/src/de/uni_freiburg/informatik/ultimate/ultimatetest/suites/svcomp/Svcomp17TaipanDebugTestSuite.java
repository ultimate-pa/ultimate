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
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ConversionContext;
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
				new ColumnDefinition("TraceCheckerStatistics_NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantCoveringCapability", "ICC", ConversionContext.Percent(true, 2),
						Aggregate.Ignore, Aggregate.Average), };
	}
	
	// Mapping:
	// AutomizerC_WitnessPrinter.xml -> TaipanReach.xml
	// AutomizerC.xml -> TaipanWitnessValidation.xml
	// TaipanMemDerefMemtrack.xml -> AutomizerC_WitnessPrinter.xml
	
	// @formatter:off
	private static final Object[] TESTCASES = {
			// WARNING: The following list is incomplete! Eclipse does not allow to save more than the number of lines
			// in this files with enabled auto-formatter (stack overflow exception). Therefore, this is just an excerpt.

			// Differences between utaipan and uautomizer
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-ControlFlow.xml.bz2.merged.xml

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Arrays.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--hwmon--nct6775.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--u132-hcd.ko_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/avg05_true-unreach-call.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/avg10_true-unreach-call.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/sum05_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/sum10_true-unreach-call.i"),

			// ****** utaipan: "unknown", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/reducercommutativity/rangesum60_false-unreach-call.i"),

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--virtio_blk.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--virtio_blk.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--xen-blkfront.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--block--xen-blkfront.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--input--touchscreen--usbtouchscreen.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--input--touchscreen--usbtouchscreen.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--misc--sgi-gru--gru.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--misc--sgi-gru--gru.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--can--janz-ican3.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--can--janz-ican3.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--ethernet--smsc--smc91c92_cs.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--net--ethernet--smsc--smc91c92_cs.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--scsi--megaraid.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--scsi--megaraid.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--isp116x-hcd.ko_false-unreach-call.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--usb--host--isp116x-hcd.ko_false-unreach-call.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Heap.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-queue_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-buckets_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-queue_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-sorted_false-unreach-call_false-valid-memcleanup.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext2-properties/list_and_tree_cnstr_false-unreach-call.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "unknown" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-BitVectors.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_1_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_2_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_3_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_6_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ssh-simplified/s3_srvr_8_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_1_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_2_alt_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_2_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_3_alt_true-unreach-call_true-no-overflow.BV.c.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/s3_srvr_3_true-unreach-call_true-no-overflow.BV.c.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "ERROR (1)", uautomizer: "unknown" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			             "examples/svcomp/bitvector/modulus_true-unreach-call_true-no-overflow.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_1652.results.sv-comp17.Overflows-BitVectors.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.UNBOUNDED.pals.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.UNBOUNDED.pals.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1651.results.sv-comp17.ConcurrencySafety-Main.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "false(unreach-call)" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.UNBOUNDED.pals.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/seq-mthreaded/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.UNBOUNDED.pals.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_lazy_false-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_stateful_true-unreach-call.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-pthread/cs_sync_true-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_2calls_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/afterrec_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_2_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_4_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_6_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id2_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/id_i5_o5_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_10x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_15x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_20x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_25x0_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_2x3_false-unreach-call_true-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/sum_non_false-unreach-call_true-termination.c"),

			// ****** utaipan: "OUT OF MEMORY", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-intel-e1000-e1000_true-unreach-call.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-linux-3.14/linux-3.14__complex_emg__linux-alloc-spinlock__drivers-net-ethernet-qlogic-qlge-qlge_true-unreach-call.cil.c"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/float-benchs/Muller_Kahan_true-unreach-call.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/seq-mthreaded/rekcba_aso_false-unreach-call.4.M1.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-Loops.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loops/eureka_05_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loops/matrix_true-unreach-call_true-termination.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/loop-acceleration/diamond_true-unreach-call1_true-termination.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loops/s3_false-unreach-call.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/loops/s3_false-unreach-call.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-Arrays.xml.bz2.merged.xml

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/ldv-memsafety/memleaks_test13_true-valid-memsafety.i"),
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/array-memsafety/lis-alloca_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/array-memsafety/lis-alloca_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			// utaipan.2017-01-14_1736.results.sv-comp17.Termination-MainControlFlow.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_10_true-unreach-call.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_15_true-unreach-call.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/recursive-simple/fibo_2calls_10_true-unreach-call.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1615.results.sv-comp17.MemSafety-LinkedLists.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "unknown" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-simple-white-blue_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-simple-white-blue_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/list_flag_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/list_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/simple_built_from_end_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/simple_true-unreach-call_false-valid-memtrack.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-properties/splice_true-unreach-call_false-valid-memtrack.i"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "false(valid-deref)" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/dll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-01_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/forester-heap/sll-rb-cnstr_1_false-unreach-call_false-valid-deref.i"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/ldv-memsafety/memleaks_test23_3_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/heap-manipulation/sll_to_dll_rev_true-unreach-call_true-valid-memsafety.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_1736.results.sv-comp17.Termination-MainHeap.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "TIMEOUT", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/diskperf_simpl1_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-valid-memsafety_true-termination.cil.c"),

			// ****** utaipan: "unknown", uautomizer: "TIMEOUT" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product18_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/product-lines/email_spec3_product24_false-unreach-call_true-termination.cil.c"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(unreach-call)", uautomizer: "true" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/cdaudio_simpl1_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/floppy_simpl4_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/ntdrivers-simplified/kbfiltr_simpl2_false-unreach-call_true-valid-memsafety_true-termination.cil.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_14_false-unreach-call_true-valid-memsafety_false-termination.c"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			             "examples/svcomp/locks/test_locks_15_false-unreach-call_true-valid-memsafety_false-termination.c"),

			// ****** utaipan: "false(valid-free)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-free.i"),

			// ****** utaipan: "ERROR", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/loop-invgen/heapsort_true-unreach-call_true-termination.i"),
			// End of multiple calls of utaipan

			// ****** utaipan: "false(valid-deref)", uautomizer: "TIMEOUT" ******
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml",
			             "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
			             "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			// utaipan.2017-01-14_0946.results.sv-comp17.ReachSafety-ECA.xml.bz2.merged.xml

			// ****** utaipan: "witness invalid (true)", uautomizer: "true" ******
			// Multiple calls to utaipan with different settings were performed
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			   new Triple<>("AutomizerC_WitnessPrinter.xml",
			                "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			                "examples/svcomp/bitvector/soft_float_4_true-unreach-call_true-no-overflow.c.cil.c"),
			// End of multiple calls of utaipan
	};
	// @formatter:on
}
