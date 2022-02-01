/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
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
 * Test for the different versions of incremental inclusion.
 * Run this as a "JUnit Plug-in Test".
 * The results will be written to the following folder.
 * trunk/source/UltimateTest/target/surefire-reports/de.uni_freiburg.informatik.ultimatetest.traceabstraction.IncrementalInclusionTest
 * 
 * Please remember to use "-ea" as VM argument for testing (because bugs will be
 * found earlier).
 * Please do not use "-ea" as VM argument for benchmarking (because settings with
 * a lot of assert statements will have a disadvantage)
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class IncrementalInclusionTest extends
		AbstractTraceAbstractionTestSuite {
	
	
	/** Limit the number of files per directory that are used. */
	private static int mFilesPerDirectoryLimit = 1000;
	
	private static final DirectoryFileEndingsPair[] s_SVCOMP_Programs = {
//		/*** Category 1. Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		
//		/*** Category 2. Bit Vectors ***/
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
//		
//		/*** Category 4. Control Flow and Integer Variables ***/
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
//		
		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
//		
//		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		
//
//		/*** Category 8. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//		
//		/*** Category 9. Sequentialized Concurrent Programs ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		/*** Category 10. incremental inclusion test examples ***/
//		new DirectoryFileEndingsPair("examples/svcomp/Incremental-Inclusion test examples/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/Incremental-Inclusion test examples/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
	};
	/**
	 * List of path. Ultimate will be run for each program that you find in
	 * one of there paths.
	 */
	private static final String[] s_UltimateRepository_Programs = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
//		"examples/programs/toy",
//		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
	};
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] s_Settings = {
//		"automizer/incrementalInclusion/Difference.epf",
		"automizer/incrementalInclusion/IncrementalInclusionViaDifference.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2_DeadEnd_Remove.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2_DeadEnd_Remove_AntiChain.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2_DeadEnd_Remove_AntiChain_2Stacks.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion2_DeadEnd_Remove_AntiChain_2Stacks_MultipleCE.epf",		
//		"automizer/incrementalInclusion/IncrementalInclusion3.epf",
// 		"automizer/incrementalInclusion/IncrementalInclusion3_2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion4.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion4_2.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion5.epf",
//		"automizer/incrementalInclusion/IncrementalInclusion5_2.epf",
//		"automizer/incrementalInclusion/nonDeterministic/Difference.epf",
		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusionViaDifference.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion2.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion2_DeadEnd_Remove.epf",
		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion2_DeadEnd_Remove_AntiChain.epf",
		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion2_DeadEnd_Remove_AntiChain_2Stacks.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion2_DeadEnd_Remove_AntiChain_2Stacks_MultipleCE.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion3.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion3_2.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion4.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion4_2.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion5.epf",
//		"automizer/incrementalInclusion/nonDeterministic/IncrementalInclusion5_2.epf",
	};
	
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 30 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : s_Settings) {
			addTestCase("AutomizerCInline.xml", 
					setting, 
					s_SVCOMP_Programs);
		}
		
		for (final String setting : s_Settings) {
			addTestCase(
					"AutomizerBplInline.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".bpl"});
		}
		for (final String setting : s_Settings) {
			addTestCase(
					"AutomizerCInline.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}

	
}
