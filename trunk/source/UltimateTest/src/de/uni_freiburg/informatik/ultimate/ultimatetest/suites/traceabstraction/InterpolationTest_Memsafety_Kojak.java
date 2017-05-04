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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class InterpolationTest_Memsafety_Kojak extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
//	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	private static int mFilesPerDirectoryLimit = 1;
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs_Deref = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
	};
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs_DerefFreeMemtrack = {
		/*** Category 3. Heap Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
	};

	
	
	private static final String[] mCurrentBugs_Deref = {
		};
	
	private static final String[] mCurrentBugs_DerefFreeMemtrack = {
//			"examples/programs/regression",
//			"examples/programs/quantifier/regression",
		};


	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final String[] mSettings = {
//		"automizer/interpolation/DerefFreeMemtrack-32bit-Princess-TreeInterpolation-Integer.epf",
////		"automizer/interpolation/DerefFreeMemtrack-32bit-SMTInterpol-FPandBP-Integer.epf",
//		"automizer/interpolation/DerefFreeMemtrack-32bit-SMTInterpol-TreeInterpolation-Integer.epf",
//		"automizer/interpolation/DerefFreeMemtrack-32bit-Z3-BP-Integer.epf",
//		"automizer/interpolation/DerefFreeMemtrack-32bit-Z3-FP-Integer.epf",
//		"automizer/interpolation/DerefFreeMemtrack-32bit-Z3-FPandBP-Integer.epf",
//		"automizer/interpolation/DerefFreeMemtrack-32bit-Z3-NestedInterpolation-Integer.epf",
		
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-iZ3-NestedInterpolation-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Princess-TreeInterpolation-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-SMTInterpol-TreeInterpolation-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-LV-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-FP-UC-LV-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-LV-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-Integer.epf",
		"kojak/interpolation/memsafety/DerefFreeMemtrack-32bit-Z3-BP-UC-LV-Integer.epf",
	};
	
	
	
	private static final String[] mCToolchains = {
			"KojakC.xml"
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDirectoryFileEndingsPairs_Deref);
				addTestCase(toolchain, setting, mCurrentBugs_Deref, new String[] {".c", ".i"});
			}
		}
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDirectoryFileEndingsPairs_DerefFreeMemtrack);
				addTestCase(toolchain, setting, mCurrentBugs_DerefFreeMemtrack, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
