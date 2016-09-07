/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class CraigInterpolationTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] mDirectories = {
//		"examples/programs/regression",
//		"examples/programs/quantifier",
		"examples/programs/recursive/regression",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
//		"examples/svcomp/recursive/",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 100 * 1000;
	}

	private static final boolean s_Boogie_TreeInterpolants = true;
	private static final boolean s_C_TreeInterpolants = true;
	private static final boolean s_Boogie_NestedInterpolants = true;
	private static final boolean s_C_NestedInterpolants = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants) {
			addTestCase(
					"AutomizerBpl.xml",
					"automizer/TreeInterpolants.epf",
				    mDirectories,
				    new String[] {".bpl"});
		} 
		if (s_C_TreeInterpolants) {
			addTestCase(
					"AutomizerC.xml",
					"automizer/TreeInterpolants.epf",
				    mDirectories,
				    new String[] {".c", ".i"});
		}
		
		if (s_Boogie_NestedInterpolants) {
			addTestCase(
					"AutomizerBpl.xml",
					"automizer/NestedInterpolants.epf",
				    mDirectories,
				    new String[] {".bpl"});
		} 
		if (s_C_NestedInterpolants) {
			addTestCase(
					"AutomizerC.xml",
					"automizer/NestedInterpolants.epf",
				    mDirectories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}
}
