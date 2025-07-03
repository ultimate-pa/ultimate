/*
 * Copyright (C) 2925 Peter Ritter
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
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;

public class LlvmirToBoogieTest extends AbstractTraceAbstractionTestSuite {

	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;

	/**
	 * Constructs a new test suite for the given Ultimate run definition. The commented out code is the implementation
	 * of the AbstractTraceAbstractionTestSuite - in the future, this decider should be used in this test suite.
	 */
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return super.constructITestResultDecider(ultimateRunDefinition);
		// return new NoErrorTestResultDecider(ultimateRunDefinition);
	}

	// @formatter:off
	private static final DirectoryFileEndingsPair[] mSVCOMP_Examples = {

	};

	private static final String[] mUltimateRepository = {
			"examples/programs/regression/ll",
	};

	private static final String[] mSettings = {
			"automizer/LlvmirToBoogie.epf",
	};


	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	private static final String[] mToolchains = {
			"AutomizerLl.xml",
	};


	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mToolchains) {
				addTestCase(toolchain, setting, mSVCOMP_Examples);
			}
		}

		for (final String setting : mSettings) {
			for (final String toolchain : mToolchains) {
				addTestCase(toolchain, setting, mUltimateRepository,
						new String[] {".ll"});
			}
		}
		return super.createTestCases();
	}
	// @formatter:on
}