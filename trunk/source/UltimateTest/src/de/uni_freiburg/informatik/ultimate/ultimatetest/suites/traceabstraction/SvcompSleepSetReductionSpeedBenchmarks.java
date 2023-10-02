/*
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

public class SvcompSleepSetReductionSpeedBenchmarks extends AbstractTraceAbstractionTestSuite {
	private static final int TIMEOUT = 150; // seconds

	// @formatter:off
	private static final String[] BENCHMARKS = {
			"examples/svcomp/pthread-atomic/szymanski.i",
			"examples/svcomp/pthread-wmm/safe000_tso.oepc.i",
			"examples/svcomp/pthread-wmm/safe004_tso.opt.i",
			"examples/svcomp/pthread-wmm/rfi001_power.opt.i",
			"examples/svcomp/pthread-wmm/rfi001_tso.opt.i",
			"examples/svcomp/pthread-wmm/mix041_tso.oepc.i",
			"examples/svcomp/pthread-wmm/safe005_pso.opt.i",
			"examples/svcomp/pthread-wmm/thin000_power.opt.i",
			"examples/svcomp/pthread-wmm/safe006_power.opt.i",
			"examples/svcomp/pthread-wmm/safe018_power.opt.i",
			"examples/svcomp/pthread-wmm/safe028_power.opt.i",
			"examples/svcomp/pthread-wmm/safe028_power.oepc.i",
			"examples/svcomp/pthread-wmm/thin001_power.opt.i",
			"examples/svcomp/pthread-wmm/thin002_tso.opt.i",
			"examples/svcomp/pthread-wmm/safe035_power.oepc.i",
			"examples/svcomp/pthread-wmm/mix055_pso.opt.i",
			"examples/svcomp/pthread-wmm/safe035_power.opt.i",
			"examples/svcomp/pthread-wmm/mix044_power.opt.i",
			"examples/svcomp/pthread-wmm/safe019_power.opt.i",
			"examples/svcomp/pthread-wmm/mix029_power.opt.i",
			"examples/svcomp/pthread-wmm/mix047_pso.opt.i",
			"examples/svcomp/pthread-wmm/mix040_tso.opt.i",
			"examples/svcomp/pthread-wmm/mix030_power.opt.i",

			"examples/svcomp/pthread-wmm/safe005_power.opt.i",
			"examples/svcomp/pthread-wmm/safe005_rmo.oepc.i",
			"examples/svcomp/pthread-wmm/safe005_rmo.opt.i",

			// TODO has other (Z3?) problems; debug later
			//"examples/svcomp/pthread/triangular-longer-1.i"
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
		return TIMEOUT * 1000L;
	}

	/**
	 * List of setting files, path defined relative to the folder
	 * "trunk/examples/settings/",
	 */
	private static final String[] SETTINGS_32BIT = {
		//"default/automizer/svcomp-Reach-32bit-Automizer_Default.epf"
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe.epf",
		//"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-NewStatesSleep-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleepPersistent-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleepPersistentFixedOrder-NoLbe.epf",
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
