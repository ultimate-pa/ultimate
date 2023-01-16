/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */

public class ConstrantHornClauseCompetitionTestSuite extends AbstractConstraintHornClauseSolverTestSuite {

	private static final String[] BENCHMARKS = {
		"examples/smtlib/horn/regression/",
//		"examples/local/2020chccomp/",
	};

	private static final String[] SETTINGS_TREEAUTOMIZER = {
		"chc/TreeAutomizer/TreeAutomizerStandardSettings.epf",
	};

	private static final String[] SETTINGS_UNIHORN = {
		"chc/AutomizerCHC/AutomizerCHC_No_Goto.epf",
		"default/unihorn/chccomp-Unihorn_Default.epf"
	};


	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	private static final String[] TOOLCHAINS_TREEAUTOMIZER = {
		"TreeAutomizer.xml",
	};

	private static final String[] TOOLCHAINS_UNIHORN = {
		"AutomizerCHC.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		{
			for (final String setting : SETTINGS_TREEAUTOMIZER) {
				for (final String toolchain : TOOLCHAINS_TREEAUTOMIZER) {
					addTestCase(toolchain, setting, BENCHMARKS,
							new String[] {".smt2"});
				}
			}
			for (final String setting : SETTINGS_UNIHORN) {
				for (final String toolchain : TOOLCHAINS_UNIHORN) {
					addTestCase(toolchain, setting, BENCHMARKS,
							new String[] {".smt2"});
				}
			}
		}
		return super.createTestCases();
	}


}
