/*
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
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * Test small examples on our two most common settings.
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class AutomizerRegressionTest extends AbstractTraceAbstractionTestSuite {
	
	private static final String[] m_UltimateRepository_ForwardPredicates = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};
	
	private static final String[] m_UltimateRepository_TreeInterpolation = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};

	
	
	private static final String[] m_Settings_ForwardPredicates = {
		"automizer/ForwardPredicates.epf",
	};
	
	private static final String[] m_Settings_TreeInterpolation = {
		"automizer/TreeInterpolants.epf",
	};

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}
	
	private static final String[] m_BoogieToolchains = {
		"AutomizerBpl.xml",
//		"AutomizerBplInline.xml",
	};
	
	private static final String[] m_CToolchains = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		{
			// Tests with TreeInterpolation
			for (String setting : m_Settings_TreeInterpolation) {
				for (String toolchain : m_BoogieToolchains) {
					addTestCase(toolchain, setting, m_UltimateRepository_TreeInterpolation, 
							new String[] {".bpl"});
				}
			}
			for (String setting : m_Settings_TreeInterpolation) {
				for (String toolchain : m_CToolchains) {
					addTestCase(toolchain, setting, m_UltimateRepository_TreeInterpolation, 
							new String[] {".c", ".i"});
				}
			}
		}
		
		{	// Tests with ForwardPredicates
			for (String setting : m_Settings_ForwardPredicates) {
				for (String toolchain : m_BoogieToolchains) {
					addTestCase(toolchain, setting, m_UltimateRepository_ForwardPredicates, 
							new String[] {".bpl"});
				}
			}
			for (String setting : m_Settings_ForwardPredicates) {
				for (String toolchain : m_CToolchains) {
					addTestCase(toolchain, setting, m_UltimateRepository_ForwardPredicates, 
							new String[] {".c", ".i"});
				}
			}
		}
		return super.createTestCases();
	}

	
}
