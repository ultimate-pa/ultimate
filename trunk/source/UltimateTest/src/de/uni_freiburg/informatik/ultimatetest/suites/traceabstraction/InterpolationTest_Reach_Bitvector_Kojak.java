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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class InterpolationTest_Reach_Bitvector_Kojak extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
//	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	private static int mFilesPerDirectoryLimit = 12;
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/reducercommutativity/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		
		/*** Category 2. Bit Vectors ***/
		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/bitvector-loops/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		

		/*** Category 3. Heap Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		
		/*** Category 5. Control Flow and Integer Variables ***/
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,

		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 8. Software Systems ***/
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.8/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-4.2-rc1/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-challenges/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/busybox-1.22.0/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
	};
	
	
	private static final String[] mCurrentBugs = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/regression",
	};
	
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final String[] mSettings = {
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-NestedInterpolation-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-FPandBP-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-FP-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-BP-Bitvector.epf",
		
		"kojak/interpolation/bitvector/Reach-32bit-iZ3-NestedInterpolation-Bitvector.epf",

//		"kojak/interpolation/bitvector/Reach-32bit-Z3-FP-Bitvector.epf",
//		"kojak/interpolation/bitvector/Reach-32bit-Z3-FP-LV-Bitvector.epf",
//		"kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-Bitvector.epf",
		"kojak/interpolation/bitvector/Reach-32bit-Z3-FP-UC-LV-Bitvector.epf",
//		"kojak/interpolation/bitvector/Reach-32bit-Z3-BP-Bitvector.epf",
//		"kojak/interpolation/bitvector/Reach-32bit-Z3-BP-LV-Bitvector.epf",
//		"kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-Bitvector.epf",
		"kojak/interpolation/bitvector/Reach-32bit-Z3-BP-UC-LV-Bitvector.epf",
	};
	
	private static final String[] mCToolchains = {
			"KojakC.xml"
	};
	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mDirectoryFileEndingsPairs);
				addTestCase(toolchain, setting, mCurrentBugs, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
