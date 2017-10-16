/*
 * Copyright (C) 2017 Dennis Wölfing
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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoErrorTestResultDecider;

public class DangerInvariantsTest extends AbstractTraceAbstractionTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new NoErrorTestResultDecider(ultimateRunDefinition);
		// return new SomeVerificationResultTestResultDecider(ultimateRunDefinition);
	}

	private static final String[] mPrograms = {
			"examples/programs/dangerInvariants",
			// "examples/programs/regression",
			// "examples/ultimate-benchmarks/pathprograms/20170417-DifficultOverflow/MapElim",
			// "examples/ultimate-benchmarks/pathprograms/20170417-DifficultOverflow/ModNeigh-MapElim",
			// "examples/ultimate-benchmarks/pathprograms/20170417-DifficultReach/MapElim",
			// "examples/ultimate-benchmarks/pathprograms/20170417-DifficultReach/MapElim-ModNeigh",
			// "examples/ultimate-benchmarks/pathprograms/20170417-DifficultReach/ModNeigh-MapElim",
//			"examples/ultimate-benchmarks/pathprograms/",
	};

	private static final String[] mSettings = {
			"automizer/dangerInvariants/dangerInvariants.epf",
			// "automizer/dangerInvariants/dangerInvariants_Nonlinear.epf",
//			"automizer/dangerInvariants/dangerInvariantsGuessing.epf",
	};

	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final String[] mBoogieToolchains = { "InvariantSynthesisBplInline.xml" };
	private static final String[] mCToolchains = { "InvariantSynthesisCInline.xml" };

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String toolchain : mCToolchains) {
			for (final String setting : mSettings) {
				addTestCase(toolchain, setting, mPrograms, new String[] { ".c", ".i" });
			}
		}

		for (final String toolchain : mBoogieToolchains) {
			for (final String setting : mSettings) {
				addTestCase(toolchain, setting, mPrograms, new String[] { ".bpl" });
			}
		}

		return super.createTestCases();
	}
}
