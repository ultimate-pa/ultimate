/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompMemsafetyTestResultDecider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class SvcompMemsafetyBugs extends AbstractEvalTestSuite {

	// @formatter:off
	
	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_KOJAK = new Triple[] {
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-1_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2.1_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3.1_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/list-ext-properties/simple-ext_false-unreach-call_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/list-ext-properties/test-0158_1_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/memsafety/test-0158_true-valid-memsafety.i"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ntdrivers/diskperf_false-unreach-call_true-valid-memsafety.i.cil.c"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ntdrivers/diskperf_true-unreach-call_true-valid-memsafety.i.cil.c"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ntdrivers/parport_false-unreach-call_true-valid-memsafety.i.cil.c"),
			new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-DerefFreeMemtrack-32bit-Kojak_Default.epf", "examples/svcomp/ntdrivers/parport_true-unreach-call_true-valid-memsafety.i.cil.c"),
	};
	
	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_TAIPAN = new Triple[] {
			
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-1_true-valid-memsafety.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-2.1_true-valid-memsafety.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3.1_true-valid-memsafety.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3_true-valid-memsafety.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety/memleaks_test12_false-valid-free.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety/memleaks_test18_2_false-valid-memtrack.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ldv-memsafety/memleaks_test23_1_true-valid-memsafety.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/list-ext-properties/960521-1_1_false-valid-deref.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/list-ext-properties/list-ext_flag_false-unreach-call_false-valid-deref.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/memsafety/test-0220_false-valid-memtrack.i"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ntdrivers/cdaudio_true-unreach-call.i.cil.c"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ntdrivers/diskperf_false-unreach-call.i.cil.c"),
			new Triple<>("AutomizerC.xml", "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf", "examples/svcomp/ntdrivers/diskperf_true-unreach-call.i.cil.c"),
	};
	
	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_AUTOMIZER = new Triple[] {
			
			new Triple<>("AutomizerC.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf", "examples/svcomp/list-ext-properties/960521-1_1_false-valid-deref.i"),
			
			//new
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/chroot-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/echo_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/logname_true-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/mkfifo-incomplete_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/realpath_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/whoami-incomplete_true-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-64bit-Automizer_Default.epf", "examples/svcomp/busybox-1.22.0/yes_false-unreach-call_true-no-overflow_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf", "examples/svcomp/memsafety/960521-1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf", "examples/svcomp/list-ext-properties/960521-1_1_false-valid-deref.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf", "examples/svcomp/list-ext-properties/test-0158_1_true-valid-memsafety.i"),
			new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf", "examples/svcomp/ldv-memsafety/memleaks_test23_1_true-valid-memsafety.i"),
	};

	// @formatter:on

	private static final Triple<String, String, String>[] INPUTS = UNSOUND_KOJAK;

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SvcompMemsafetyTestResultDecider(ultimateRunDefinition, false);
	}

	@Override
	protected long getTimeout() {
		return 90 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String, String> triple : INPUTS) {
			addTestCase(triple.getFirst(), triple.getSecond(), triple.getThird());
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
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Trace Abstraction Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average), };
	}
}
