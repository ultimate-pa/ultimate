/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderUnreachCall;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * @author klumpp@informatik.uni-freiburg.de
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Svcomp20AutomizerConcurrentSpeedBenchmarks extends AbstractTraceAbstractionTestSuite {

	private static final boolean USE_SAFE_BENCHMARKS = true;
	private static final boolean USE_UNSAFE_BENCHMARKS = true;
	private static final int TIMEOUT_IN_SECONDS = 120;

	// @formatter:off
	private static final String[] BENCHMARKS_UNSAFE_32BIT = {
		"examples/svcomp/ldv-races/race-2_2-container_of.i",
		"examples/svcomp/ldv-races/race-2_3-container_of.i", //only LBE needs time
		"examples/svcomp/ldv-races/race-3_2-container_of-global.i",
		"examples/svcomp/ldv-races/race-4_2-thread_local_vars.i",
		"examples/svcomp/pthread-atomic/read_write_lock-2.i",
		"examples/svcomp/pthread/triangular-2.i",
		"examples/svcomp/pthread/singleton.i",
		"examples/svcomp/pthread/stack-2.i",
	};

	private static final String[] BENCHMARKS_SAFE_32BIT = {
		"examples/svcomp/ldv-races/race-4_2-thread_local_vars.i",
		"examples/svcomp/ldv-races/race-4_1-thread_local_vars.i",
		"examples/svcomp/pthread-atomic/qrcu-1.i",
		"examples/svcomp/pthread/triangular-1.i",
		"examples/svcomp/pthread-atomic/read_write_lock-1.i",
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
////		"default/automizer/svcomp-Reach-32bit-Automizer_Default.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-VariableLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-VariableLbe.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-Backfolding.epf",
//		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Dbo.epf",
	};

	private static final String[] TOOLCHAINS = {
		"AutomizerCInline.xml",
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
