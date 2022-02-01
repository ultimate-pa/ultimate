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

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class InterpolationTest_Reach_Bitvector_CVC4Comparison extends AbstractTraceAbstractionTestSuite {

	private static final String[] mDifferenceInPerformance = {
			"examples/svcomp/heap-manipulation/sll_to_dll_rev_false-unreach-call_false-valid-memcleanup.i",
			"examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_670x-ko--107_1a--adbbc36-1.c",
			"examples/svcomp/ldv-validator-v0.6/linux-stable-1b0b0ac-1-108_1a-drivers--net--slip.ko-entry_point_false-unreach-call.cil.out.c",
			"examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-32_7a-drivers--hid--usbhid--usbhid.ko-entry_point_true-unreach-call.cil.out.c",
			"examples/svcomp/ldv-linux-3.12-rc1/linux-3.12-rc1.tar.xz-144_2a-drivers--input--tablet--gtco.ko-entry_point_false-unreach-call.cil.out.c",
			"examples/svcomp/ldv-challenges/linux-3.14__complex_emg__linux-kernel-locking-spinlock__drivers-net-ethernet-dec-tulip-uli526x_true-unreach-call.cil.c",
			"examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_660x-ko--107_1a--adbbc36-1.c",
			"examples/svcomp/ldv-commit-tester/m0_false-unreach-call_drivers-staging-comedi-drivers-ni_pcidio-ko--107_1a--adbbc36-1.c",
			"examples/svcomp/ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-08_1a-drivers--md--md-cluster.ko-entry_point_false-unreach-call.cil.out.c",
//			"examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--wan--hdlc_ppp.ko-entry_point_false-unreach-call.cil.out.c",
			"examples/svcomp/ldv-consumption/32_7a_cilled_false-unreach-call_linux-3.8-rc1-drivers--media--rc--rc-core.ko-main.cil.out.c",
			"examples/svcomp/ldv-linux-3.4-simple/32_7_cilled_false-unreach-call_const_ok_linux-32_1-drivers--mtd--chips--cfi_cmdset_0001.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c",
			"examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--ethernet--8390--8390.ko-entry_point_false-unreach-call.cil.out.c",
			"examples/svcomp/ldv-linux-3.16-rc1/205_9a_array_unsafes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--ppp--ppp_synctty.ko-entry_point_false-unreach-call.cil.out.c",
	};
	
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 120 * 1000;
	}

	private static final String[] mSettings = {
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-NestedInterpolation-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcSpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcSp-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-SpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-Sp-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcWpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcWp-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-WpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-Wp-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-FPandBP-Bitvector.epf",
		"automizer/interpolation/bitvector/Reach-32bit-CVC4-IcSpLv-Bitvector.epf",
		"automizer/interpolation/bitvector/Reach-32bit-CVC4stanford-IcSpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-CVC4-IcWpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-CVC4-FPandBP-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-MathSAT-IcSpLv-Bitvector.epf",
	};

	
	private static final String[] mCToolchains = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
	};
	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDifferenceInPerformance, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
