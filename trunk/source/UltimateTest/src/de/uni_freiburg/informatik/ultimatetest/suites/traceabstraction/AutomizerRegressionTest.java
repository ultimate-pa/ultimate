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
	
	private static final String[] mUltimateRepository_ForwardPredicates = {
		"examples/programs/regression",
		"examples/programs/quantifier/regression",
//		"examples/programs/recursive/regression",
//		"examples/programs/toy",
	};
	
	private static final String[] mUltimateRepository_TreeInterpolation = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursive/regression",
//		"examples/programs/toy",
	};

	
	
	private static final String[] mSettings_ForwardPredicates = {
		"automizer/ForwardPredicates.epf",
	};
	
	private static final String[] mSettings_TreeInterpolation = {
		"automizer/TreeInterpolants.epf",
	};

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}
	
	private static final String[] mBoogieToolchains = {
		"AutomizerBpl.xml",
//		"AutomizerBplInline.xml",
	};
	
	private static final String[] mCToolchains = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
	};

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		{
			// Tests with TreeInterpolation
			for (final String setting : mSettings_TreeInterpolation) {
				for (final String toolchain : mBoogieToolchains) {
					addTestCase(toolchain, setting, mUltimateRepository_TreeInterpolation, 
							new String[] {".bpl"});
				}
			}
			for (final String setting : mSettings_TreeInterpolation) {
				for (final String toolchain : mCToolchains) {
					addTestCase(toolchain, setting, mUltimateRepository_TreeInterpolation, 
							new String[] {".c", ".i"});
				}
			}
		}
		
		{	// Tests with ForwardPredicates
			for (final String setting : mSettings_ForwardPredicates) {
				for (final String toolchain : mBoogieToolchains) {
					addTestCase(toolchain, setting, mUltimateRepository_ForwardPredicates, 
							new String[] {".bpl"});
				}
			}
			for (final String setting : mSettings_ForwardPredicates) {
				for (final String toolchain : mCToolchains) {
					addTestCase(toolchain, setting, mUltimateRepository_ForwardPredicates, 
							new String[] {".c", ".i"});
				}
			}
		}
		return super.createTestCases();
	}

	
}
