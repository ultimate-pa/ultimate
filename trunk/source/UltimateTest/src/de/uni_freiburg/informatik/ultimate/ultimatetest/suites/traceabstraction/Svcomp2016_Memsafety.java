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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp2016_Memsafety extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
//	private static int mFilesPerDirectoryLimit = 5;
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs_Deref = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
	};
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs_DerefFreeMemtrack = {
		/*** Category 3. Heap Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
	};

	
	
	private static final String[] mCurrentBugs_Deref = {
		};
	
	private static final String[] mCurrentBugs_DerefFreeMemtrack = {
//			"examples/svcomp/array-memsafety/openbsd_cbzero-alloca_true-valid-memsafety.i"

			
//			////////////////////////////////////////////////////////////////
//			// Soundness problems detected on 2015-11-03
//			// UNSAFE_FREE (Expected:SAFE)
//			"examples/svcomp/list-ext-properties/test-0158_1_true-valid-memsafety.i",
//			
//			// UNSAFE_DEREF (Expected:UNSAFE_MEMTRACK)
//			"examples/svcomp/memsafety/20020406-1_false-valid-memtrack.i",
//			
//			//UNSAFE_MEMTRACK (Expected:SAFE)
//			"examples/svcomp/ldv-memsafety/memleaks_test20_true-valid-memsafety.i",
//			"examples/svcomp/ldv-memsafety/memleaks_test21_true-valid-memsafety.i",
//			
//			//UNSAFE_DEREF (Expected:SAFE)
//			"examples/svcomp/ldv-memsafety/memleaks_test22_1_true-valid-memsafety.i",
//			"examples/svcomp/ldv-memsafety/memleaks_test22_2_true-valid-memsafety.i",
//			"examples/svcomp/ldv-memsafety/memleaks_test22_3_true-valid-memsafety.i",
//			////////////////////////////////////////////////////////////////
			
			// some other problems
//			"examples/svcomp/ldv-memsafety/memleaks_test18_true-valid-memsafety.i",
//			"examples/svcomp/array-memsafety/cstrncat-alloca_true-valid-memsafety.i",
//			"examples/svcomp/array-memsafety/cstrchr_unsafe_false-valid-deref.i",
//			"examples/svcomp/ldv-memsafety/memleaks_test19_true-valid-memsafety.i",
//			"examples/svcomp/ldv-memsafety/memleaks_test17_2_true-valid-memsafety.i",
//			"examples/svcomp/array-memsafety/openbsd_cstrstr-alloca_true-valid-memsafety.i",
		};


	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 300 * 1000;
	}

	private static final String[] mSettings_Deref = {
		"svcomp2016/svcomp-Deref-32bit-Automizer_Default.epf",
		"svcomp2016/svcomp-Deref-32bit-Automizer_Bitvector.epf",
	};
	
	private static final String[] mSettings_DerefFreeMemtrack = {
		"svcomp2016/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf",
		"svcomp2016/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf",
	};

	
	
	private static final String[] mCToolchains = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings_Deref) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDirectoryFileEndingsPairs_Deref);
				addTestCase(toolchain, setting, mCurrentBugs_Deref, new String[] {".c", ".i"});
			}
		}
		for (final String setting : mSettings_DerefFreeMemtrack) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDirectoryFileEndingsPairs_DerefFreeMemtrack);
				addTestCase(toolchain, setting, mCurrentBugs_DerefFreeMemtrack, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
