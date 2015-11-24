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

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp2016_Memsafety extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
//	private static int m_FilesPerDirectoryLimit = 5;
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs_Deref = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
	};
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs_DerefFreeMemtrack = {
		/*** Category 3. Heap Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
	};

	
	
	private static final String[] m_CurrentBugs_Deref = {
		};
	
	private static final String[] m_CurrentBugs_DerefFreeMemtrack = {
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

	private static final String[] m_Settings_Deref = {
		"svcomp2016/svcomp-Deref-32bit-Automizer_Default.epf",
		"svcomp2016/svcomp-Deref-32bit-Automizer_Bitvector.epf",
	};
	
	private static final String[] m_Settings_DerefFreeMemtrack = {
		"svcomp2016/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf",
		"svcomp2016/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf",
	};

	
	
	private static final String[] m_CToolchains = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings_Deref) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_DirectoryFileEndingsPairs_Deref);
				addTestCases(toolchain, setting, m_CurrentBugs_Deref, new String[] {".c", ".i"});
			}
		}
		for (String setting : m_Settings_DerefFreeMemtrack) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_DirectoryFileEndingsPairs_DerefFreeMemtrack);
				addTestCases(toolchain, setting, m_CurrentBugs_DerefFreeMemtrack, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
