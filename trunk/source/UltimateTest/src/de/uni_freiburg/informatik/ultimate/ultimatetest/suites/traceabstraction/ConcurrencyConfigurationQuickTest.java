/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;

/**
 * Verifies a few simple programs with various concurrency configurations, to quickly find crashes after a change.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ConcurrencyConfigurationQuickTest extends AbstractTraceAbstractionTestSuite {

	// @formatter:off
	private static final String[] SETTINGS = {
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe-Delay.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe-New_States.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-SemanticLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-VariableLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Backfolding.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Dbo.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-Backfolding.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-SemanticLooper.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-VariableLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe-Lockstep.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe-Random42.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe-Random521.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-NoLbe-Random7777.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleepPersistentFixedOrder-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleepPersistent-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-DelaySleep-SemanticLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-NewStatesSleep-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-NewStatesSleepPersistent-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-NewStatesSleepUncond-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-None-NoLbe.epf",
		"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-POR-Persistent-NoLbe.epf",
	};

	private static final String[] BOOGIE_EXAMPLES = {
		"examples/concurrent/bpl/regression/example_interleaving.bpl",
		"examples/concurrent/bpl/regression/showcase/Peterson.bpl",
		"examples/concurrent/bpl/regression/showcase/PetersonWithBug.bpl",
	};

	private static final String[] C_EXAMPLES = {
		"examples/concurrent/pthreads/regression/forkJoinInLoop.c",
		"examples/concurrent/pthreads/regression/join_correct.c",
	};

	private static final String BOOGIE_TOOLCHAIN = "AutomizerBplInline.xml";
	private static final String C_TOOLCHAIN = "AutomizerCInline.xml";
	// @formatter:on

	@Override
	protected long getTimeout() {
		return 60L;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : SETTINGS) {
			for (final String file : BOOGIE_EXAMPLES) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(file, setting, BOOGIE_TOOLCHAIN,
						getTimeout()));
			}
			for (final String file : C_EXAMPLES) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(file, setting, C_TOOLCHAIN,
						getTimeout()));
			}
		}
		return super.createTestCases();
	}
}
