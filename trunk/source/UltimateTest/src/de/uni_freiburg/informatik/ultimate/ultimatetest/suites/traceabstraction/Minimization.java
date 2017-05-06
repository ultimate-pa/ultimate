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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Minimization extends AbstractTraceAbstractionTestSuite {
	
	
	/** Limit the number of files per directory. */
//	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	private static int mFilesPerDirectoryLimit = 25;
	
	private static final DirectoryFileEndingsPair[] s_SVCOMP_Programs = {
//			/*** Category 1. Arrays ***/
//			new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/reducercommutativity/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			
//			
//			/*** Category 2. Bit Vectors ***/
//			new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/bitvector-loops/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			
//	
//			/*** Category 3. Heap Data Structures ***/
//			new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
			
			
			/*** Category 5. Control Flow and Integer Variables ***/
			new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
			
//			new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
	
			new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
			
			new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".i" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i"}, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
			
			new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
			
			new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
			
			new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
			new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
			
//			/*** Category 8. Software Systems ***/
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.2-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			new DirectoryFileEndingsPair("examples/svcomp/ldv-challenges/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//			
//			new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
			
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
//		"automizer/minimization/TreeInterpolants-DFA_HOPCROFT_ARRAYS.epf",
//		"automizer/minimization/TreeInterpolants-MINIMIZE_SEVPA.epf",
		"automizer/minimization/TreeInterpolants-NONE.epf",
//		"automizer/minimization/TreeInterpolants-SHRINK_NWA.epf",
//		"automizer/minimization/TreeInterpolants-NWA_COMBINATOR.epf",
//		"automizer/minimization/TreeInterpolants-NWA_MAX_SAT.epf", // use with caution, does not respect timeout
//		"automizer/minimization/TreeInterpolants-NWA_MAX_SAT2.epf",
//		"automizer/minimization/TreeInterpolants-RAQ_DIRECT_SIMULATION.epf",
//		"automizer/minimization/TreeInterpolants-RAQ_DIRECT_SIMULATION_B.epf",
		"automizer/minimization/TreeInterpolants-NWA_COMBINATOR_MULTI_DEFAULT.epf",
//		"automizer/minimization/TreeInterpolants-NWA_COMBINATOR_MULTI_SIMULATION.epf",
//		"automizer/minimization/TreeInterpolants-NONE-DFS.epf",
//		"automizer/minimization/TreeInterpolants-SHRINK_NWA-DFS.epf",
//		"automizer/minimization/ForwardPredicates-NONE.epf",
//		"automizer/minimization/ForwardPredicates-SHRINK_NWA.epf",
//		"automizer/minimization/ForwardPredicates-NWA_MAX_SAT2.epf",
//		"automizer/minimization/ForwardPredicates-NWA_COMBINATOR_MULTI_DEFAULT.epf",
//		"automizer/minimization/BackwardPredicates-NWA_COMBINATOR_MULTI_DEFAULT.epf",
//		"automizer/minimization/Twotrack-NWA_COMBINATOR_MULTI_DEFAULT.epf",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : s_Settings) {
			addTestCase("AutomizerC.xml", 
					setting, 
					s_SVCOMP_Programs);
		}
		
		for (final String setting : s_Settings) {
			addTestCase(
					"AutomizerBpl.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".bpl"});
		}
		for (final String setting : s_Settings) {
			addTestCase(
					"AutomizerC.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}

}
