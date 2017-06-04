/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompReachTestResultDecider;

/**
 * Testsuite that contains benchmarks where we get a timeout during
 * error localization.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class ErrorLocalizationSvcomp17Difficult extends AbstractTraceAbstractionTestSuite {

	// @formatter:off
	private static final String[] BENCHMARKS = {
//            "examples/svcomp/floats-cdfpl/newton_1_6_false-unreach-call.i",
//            "examples/svcomp/floats-cdfpl/newton_1_7_false-unreach-call.i",
            "examples/svcomp/forester-heap/dll-queue_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/forester-heap/dll-sorted_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/forester-heap/dll-token_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/forester-heap/sll-buckets_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/heap-manipulation/sll_to_dll_rev_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/heap-manipulation/tree_false-unreach-call_false-valid-deref.i",
            "examples/svcomp/heap-manipulation/tree_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-net-slip-ko--108_1a--1b0b0ac-1.c",
            "examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_65xx-ko--107_1a--adbbc36-1.c",
            "examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_660x-ko--107_1a--adbbc36-1.c",
            "examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_670x-ko--107_1a--adbbc36-1.c",
            "examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-usb-gadget-g_printer-ko--106_1a--2b9ec6c.c",
            "examples/svcomp/ldv-commit-tester/main0_false-unreach-call_drivers-net-wireless-ath-carl9170-carl9170-ko--32_7a--8a9f335-1.c",
            "examples/svcomp/ldv-commit-tester/main3_false-unreach-call_drivers-staging-usbip-vhci-hcd-ko--132_1a--927c3fa.c",
            "examples/svcomp/ldv-consumption/32_7a_cilled_false-unreach-call_linux-3.8-rc1-drivers--pcmcia--pcmcia_rsrc.ko-main.cil.out.c",
            "examples/svcomp/ldv-consumption/linux-3.8-rc1-32_7a-drivers--net--wireless--mwl8k.ko-ldv_main0_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-linux-3.0/module_get_put-drivers-tty-synclink_gt.ko_false-unreach-call.cil.out.i.pp.i",
            "examples/svcomp/ldv-linux-3.0/usb_urb-drivers-hid-usbhid-usbmouse.ko_false-unreach-call.cil.out.i.pp.i",
            "examples/svcomp/ldv-linux-3.0/usb_urb-drivers-net-can-usb-ems_usb.ko_false-unreach-call.cil.out.i.pp.i",
            "examples/svcomp/ldv-linux-3.0/usb_urb-drivers-usb-misc-iowarrior.ko_false-unreach-call.cil.out.i.pp.i",
            "examples/svcomp/ldv-linux-3.12-rc1/linux-3.12-rc1.tar.xz-144_2a-drivers--input--tablet--gtco.ko-entry_point_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wireless--mwifiex--mwifiex_pcie.ko-entry_point_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-linux-3.4-simple/32_7_cilled_false-unreach-call_const_ok_linux-32_1-drivers--usb--image--microtek.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c",
            "examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_false-unreach-call_ok_linux-43_1a-drivers--misc--sgi-xp--xpc.ko-ldv_main3_sequence_infinite_withcheck_stateful.cil.out.c",
            "examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_false-unreach-call_ok_linux-43_1a-drivers--usb--gadget--mv_udc.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c",
            "examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_false-unreach-call_ok_linux-43_1a-drivers--usb--gadget--pch_udc.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c",
            "examples/svcomp/ldv-linux-3.7.3/main0_false-unreach-call_drivers-net-wireless-mwl8k-ko---32_7a--linux-3.7.3.c",
            "examples/svcomp/ldv-linux-3.7.3/main0_false-unreach-call_drivers-vhost-tcm_vhost-ko--32_7a--linux-3.7.3.c",
            "examples/svcomp/ldv-linux-3.7.3/main1_false-unreach-call_drivers-vhost-vhost_net-ko--32_7a--linux-3.7.3.c",
            "examples/svcomp/ldv-regression/recursive_list.c_false-unreach-call.i",
            "examples/svcomp/ldv-regression/rule57_ebda_blast.c_false-unreach-call.i",
            "examples/svcomp/ldv-validator-v0.6/linux-stable-39a1d13-1-101_1a-drivers--block--virtio_blk.ko-entry_point_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-validator-v0.6/linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-validator-v0.8/linux-stable-a450319-1-144_1a-drivers--input--tablet--acecad.ko-entry_point_ldv-val-v0.8_false-unreach-call.cil.out.c",
            "examples/svcomp/ldv-validator-v0.8/linux-stable-af3071a-1-130_7a-drivers--hwmon--s3c-hwmon.ko-entry_point_ldv-val-v0.8_false-unreach-call.cil.out.c",
            "examples/svcomp/list-ext2-properties/simple_and_skiplist_2lvl_false-unreach-call.i",
            "examples/svcomp/list-properties/splice_false-unreach-call_false-valid-memcleanup.i",
            "examples/svcomp/ntdrivers-simplified/floppy_simpl3_false-unreach-call_true-valid-memsafety_true-termination.cil.c",
            "examples/svcomp/ssh/s3_clnt.blast.04_false-unreach-call.i.cil.c",
            "examples/svcomp/ssh/s3_srvr.blast.01_false-unreach-call.i.cil.c",
            "examples/svcomp/ssh/s3_srvr.blast.03_false-unreach-call.i.cil.c",
            "examples/svcomp/ssh/s3_srvr.blast.04_false-unreach-call.i.cil.c",
            "examples/svcomp/systemc/token_ring.03_false-unreach-call_false-termination.cil.c",
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
		return 60 * 1000;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS = {
		"automizer/ErrorLocalization/Reach-Automizer_Default.epf",
//		"automizer/ErrorLocalization/Reach-Automizer_Bitvector.epf",
//		"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf",
//		"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf",
	};
	

	
	
	private static final String[] TOOLCHAINS = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
//		"AutomizerCInlineTransformed.xml",
	};
	// @formatter:on

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String benchmark : BENCHMARKS) {
			for (final String toolchain : TOOLCHAINS) {
				for (final String setting : SETTINGS) {
					addTestCase(toolchain, setting, benchmark);
				}
			}
		}
		return super.createTestCases();
	}

}
