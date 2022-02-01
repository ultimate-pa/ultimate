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
public class Svcomp_Reach_PreciseMemoryModel extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 2. Bit Vectors ***/
		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 4. Control Flow and Integer Variables ***/
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}) , // contains "n.c24_false-unreach-call.i", which's test doesn't terminate
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, mFilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 7. Memory Safety ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,

		/*** Category 8. Recursive ***/
		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		
		/*** Category 9. Sequentialized Concurrent Programs ***/
		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		
		
		/*** Category 10. Simple  ***/
		/* This category uses in fact the simple memory model, but it is sound to verify it using the precise memory model */
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean mAutomizerWithForwardPredicates = true;
	private static final boolean mAutomizerWithBackwardPredicates = false;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mAutomizerWithForwardPredicates) {
			addTestCase("AutomizerC.xml", 
					"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", 
					mDirectoryFileEndingsPairs);
		}
		if (mAutomizerWithBackwardPredicates) {
			addTestCase("AutomizerC.xml", 
					"automizer/BackwardPredicates_SvcompReachPreciseMM.epf", 
					mDirectoryFileEndingsPairs);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
