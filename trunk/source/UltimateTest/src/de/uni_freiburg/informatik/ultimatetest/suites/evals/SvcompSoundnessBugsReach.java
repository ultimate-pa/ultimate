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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class SvcompSoundnessBugsReach extends AbstractEvalTestSuite {

	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_TAIPAN = new Triple[] {
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-challenges/linux-3.14__linux-drivers-clk1__drivers-net-ethernet-cadence-macb_true-unreach-call.cil.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-consumption/32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-drivers--media--dvb-core--dvb-core.ko-ldv_main5_sequence_infinite_withcheck_stateful.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-consumption/32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-sound--core--snd-rawmidi.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.0/module_get_put-drivers-block-pktcdvd.ko_false-unreach-call.cil.out.i.pp.i"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--arcnet--rfc1051.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wan--lapbether.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wan--hdlc_x25.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/43_2a_bitvector_linux-3.16-rc1.tar.xz-43_2a-drivers--scsi--megaraid--megaraid_mm.ko-entry_point_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-3.7.3/main4_false-unreach-call_drivers-scsi-mpt2sas-mpt2sas-ko--32_7a--linux-3.7.3.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--char--ipmi--ipmi_msghandler.ko_true-unreach-call.cil.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--media--rc--lirc_dev.ko_true-unreach-call.cil.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--char--raw.ko-entry_point_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--media--usb--em28xx--em28xx-dvb.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-32_7a-drivers--net--usb--r8152.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-43_2a-drivers--scsi--megaraid--megaraid_mm.ko-entry_point_false-unreach-call.cil.out.c"),
	};

	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_KOJAK = new Triple[] {
		new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-Reach-32bit-Kojak_Default.epf", "examples/svcomp/bitvector/gcd_1_true-unreach-call_true-no-overflow.i"),
		new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-Reach-32bit-Kojak_Default.epf", "examples/svcomp/bitvector/sum02_true-unreach-call_true-no-overflow.i"),
		new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-Reach-32bit-Kojak_Default.epf", "examples/svcomp/reducercommutativity/avg60_true-unreach-call.i"),
		new Triple<>("KojakC_WitnessPrinter.xml", "svcomp2017/kojak/svcomp-Reach-64bit-Kojak_Default.epf", "examples/svcomp/ldv-consumption/32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-drivers--media--v4l2-core--videobuf-dma-contig.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"),
	};

	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] UNSOUND_AUTOMIZER = new Triple[] {

		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-challenges/linux-3.14__linux-drivers-clk1__drivers-net-ethernet-cadence-macb_true-unreach-call.cil.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-consumption/32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-drivers--media--dvb-core--dvb-core.ko-ldv_main5_sequence_infinite_withcheck_stateful.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-consumption/32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-sound--core--snd-rawmidi.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-consumption/linux-3.8-rc1-32_7a-drivers--scsi--mpt3sas--mpt3sas.ko-ldv_main4_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.0/module_get_put-drivers-block-pktcdvd.ko_false-unreach-call.cil.out.i.pp.i"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--arcnet--capmode.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--arcnet--rfc1051.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wan--lapbether.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wan--hdlc_x25.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.16-rc1/43_2a_bitvector_linux-3.16-rc1.tar.xz-43_2a-drivers--scsi--megaraid--megaraid_mm.ko-entry_point_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-3.7.3/main4_false-unreach-call_drivers-scsi-mpt2sas-mpt2sas-ko--32_7a--linux-3.7.3.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-4.0-rc1-mav/linux-4.0-rc1---drivers--media--rc--lirc_dev.ko_true-unreach-call.cil.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--char--raw.ko-entry_point_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--media--usb--em28xx--em28xx-dvb.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-32_7a-drivers--net--usb--r8152.ko-entry_point_true-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-43_2a-drivers--scsi--megaraid--megaraid_mm.ko-entry_point_false-unreach-call.cil.out.c"),
		new Triple<>("AutomizerC_WitnessPrinter.xml", "svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "examples/svcomp/ldv-validator-v0.8/linux-stable-064368f-1-111_1a-drivers--media--radio--si4713-i2c.ko-entry_point_ldv-val-v0.8_false-unreach-call.cil.out.c"),
	};

	private static final Triple<String, String, String>[] INPUTS = CoreUtil.concatAll(UNSOUND_TAIPAN, UNSOUND_KOJAK, UNSOUND_AUTOMIZER);

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SvcompReachTestResultDecider(ultimateRunDefinition, false);
	}

	@Override
	protected long getTimeout() {
		return 15 * 60 * 1000;
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
