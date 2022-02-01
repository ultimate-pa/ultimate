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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessBugs extends AbstractEvalTestSuite {
	private static final String[] ALL_C = new String[] { ".c", ".i" };

	private Collection<UltimateRunDefinition> createDefs() {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<>();
		// rtr.addAll(produceWitnessSV("locks"));
		// rtr.addAll(produceWitnessSV("loops/veris.c_NetBSD-libc__loop_true-unreach-call.c"));
		// rtr.addAll(verifyWitnessSV("loops/veris.c_NetBSD-libc__loop_true-unreach-call.c"));
		// rtr.addAll(produceWitnessSV("locks/test_locks_5_true-unreach-call_false-termination.c"));
		// rtr.addAll(verifyWitnessSV("locks/test_locks_5_true-unreach-call_false-termination.c"));

		// rtr.addAll(produceAndVerifyWitnessSV(
		// "ldv-linux-4.2-rc1/linux-4.2-rc1.tar.xz-43_2a-drivers--net--appletalk--ipddp.ko-entry_point_true-unreach-call.cil.out.c"));
		// rtr.addAll(produceAndVerifyWitnessSV("ldv-regression/ex3_forlist.c_true-unreach-call.i"));
		// rtr.addAll(produceAndVerifyWitnessSV("ssh-simplified/s3_clnt_1_true-unreach-call.cil.c"));
		// rtr.addAll(produceAndVerifyWitnessSV("locks/test_locks_7_true-unreach-call_false-termination.c"));
		// rtr.addAll(produceAndVerifyWitnessSV("product-lines/minepump_spec5_product01_true-unreach-call.cil.c"));
		rtr.addAll(produceAndVerifyWitnessSV("ldv-regression/mutex_lock_int.c_false-unreach-call.cil.c"));
		// rtr.addAll(produceAndVerifyWitnessSV("floats-cbmc-regression/float11_true-unreach-call.i"));
		// rtr.addAll(produceAndVerifyWitnessSV(
		// "ldv-linux-3.4-simple/32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--staging--serqt_usb2--serqt_usb2.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"));
		// rtr.addAll(produceAndVerifyWitnessSV(
		// "ldv-linux-3.4-simple/32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--staging--serqt_usb2--serqt_usb2.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"));
		// rtr.addAll(produceAndVerifyWitnessSV(
		// "ldv-linux-3.4-simple/32_1_cilled_true-unreach-call_ok_nondet_linux-3.4-32_1-drivers--leds--ledtrig-default-on.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.c"));

		// rtr.addAll(produceWitnessSV("loop-acceleration/multivar_true-unreach-call1.i"));
		// rtr.addAll(verifyWitnessSV("loop-acceleration/multivar_true-unreach-call1.i"));
		// rtr.addAll(produceWitnessSV("loop-acceleration"));
		// rtr.addAll(verifyWitnessSV("product-lines"));
		// rtr.addAll(verifyWitnessSV("loops/array_true-unreach-call.i"));
		// rtr.addAll(produceWitnessSV("loops/trex02_true-unreach-call_true-termination.i"));
		// rtr.addAll(produceWitnessSV("recursive-simple/afterrec_true-unreach-call.c"));
		// rtr.addAll(produceWitness("examples/programs/toy/showcase/GoannaDoubleFree.c"));

		return rtr;
	}

	@Override
	protected long getTimeout() {
		return 90 * 1000 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Total time", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	/**
	 * Create test cases from quadruples (toolchain, fileendings, settingsfile, inputfiles)
	 */
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCase(createDefs());
		return super.createTestCases();
	}

	private static String sv(final String path) {
		return "examples/svcomp/" + path;
	}

	private Collection<UltimateRunDefinition> produceAndVerifyWitnessSV(final String example) {
		final List<UltimateRunDefinition> rtr = new ArrayList<>();
		rtr.addAll(produceWitnessSV(example));
		rtr.addAll(verifyWitnessSV(example));
		return rtr;
	}

	private Collection<UltimateRunDefinition> produceWitnessSV(final String example) {
		return produceWitness(sv(example));
	}

	private Collection<UltimateRunDefinition> produceWitness(final String example) {
		return UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { example }, ALL_C,
				"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "AutomizerC_WitnessPrinter.xml",
				getTimeout());
	}

	private Collection<UltimateRunDefinition> verifyWitnessSV(final String example) {
		return verifyWitness(sv(example));
	}

	private Collection<UltimateRunDefinition> verifyWitness(final String example) {
		return UltimateRunDefinitionGenerator.getRunDefinitionFromTrunkWithWitnesses(new String[] { example }, ALL_C,
				"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf", "AutomizerC.xml", getTimeout());
	}
}
