/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;

/**
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class PetriAutomizerTest extends AbstractTraceAbstractionTestSuite {

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, false);
	}

	// private static int FILES_PER_DIRECTORY_LIMIT = Integer.MAX_VALUE;

	// @formatter:off
	private static final DirectoryFileEndingsPair[] SVCOMP = {
//		/*** Category 1. Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, FILES_PER_DIRECTORY_LIMIT) ,
//
	};


	private static final String[] ULTIMATE_REPO = {
		"examples/concurrent/bpl",
		"examples/concurrent/pthreads",
	};


	/**
	 * List of path to setting files.
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 */
	private static final String[] SETTINGS = {
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-NoLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-SemanticLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-FA-VariableLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-VariableLbe.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Backfolding.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-SemanticLbe-Backfolding.epf",
			"automizer/concurrent/svcomp-Reach-32bit-Automizer_Default-noMmResRef-PN-NoLbe-Dbo.epf",
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	private static final String[] BOOGIE_TOOLCHAINS = {
		"AutomizerBplInline.xml",
	};

	private static final String[] C_TOOLCHAINS = {
		"AutomizerCInline.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : SETTINGS) {
			for (final String toolchain : C_TOOLCHAINS) {
				addTestCase(toolchain, setting, SVCOMP);
			}
		}

		for (final String setting : SETTINGS) {
			for (final String toolchain : BOOGIE_TOOLCHAINS) {
				addTestCase(toolchain, setting, ULTIMATE_REPO,
						new String[] {".bpl"});
			}
		}
		for (final String setting : SETTINGS) {
			for (final String toolchain : C_TOOLCHAINS) {
				addTestCase(toolchain, setting, ULTIMATE_REPO,
						new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}
	// @formatter:on

}
