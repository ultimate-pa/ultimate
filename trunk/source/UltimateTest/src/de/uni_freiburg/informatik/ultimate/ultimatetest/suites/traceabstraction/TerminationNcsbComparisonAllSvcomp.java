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

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SomeVerificationResultTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer.AbstractBuchiAutomizerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class TerminationNcsbComparisonAllSvcomp extends AbstractBuchiAutomizerTestSuite {

	/** Limit the number of files per directory. */

	private static int FILES_PER_DIR_LIMIT = Integer.MAX_VALUE;

//	 private static int mFilesPerDirectoryLimit = 1;
	 private static final int FILE_OFFSET = 0;

	// @formatter:off
	private static final String STANDARD_DOT_C_PATTERN = ".*.i|.*.c";
	

	private static final String ALL_C = ".*_false-unreach-call.*\\.c|.*_true-unreach-call.*\\.c|.*_false-no-overflow.*\\.c|.*_true-no-overflow.*\\.c|.*_false-valid-deref.*\\.c|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.c";
	private static final String ALL_I = ".*_false-unreach-call.*\\.i|.*_true-unreach-call.*\\.i|.*_false-no-overflow.*\\.i|.*_true-no-overflow.*\\.i|.*_false-valid-deref.*\\.i|.*_false-valid-free.*\\.c|.*_false-valid-memtrack.*\\.c|.*_true-valid-memsafety.*\\.i";

	private static final String BITVECTOR_FOLDER_DOT_C_PATTERN =
			".*_false-unreach-call.*\\.c|.*_true-unreach-call.*\\.c.cil.c";

	// private static final String STANDARD_DOT_C_PATTERN = ".*_false-unreach-call.*\\.c";
	// private static final String STANDARD_DOT_I_PATTERN = ".*_false-unreach-call.*\\.i";

	// @formatter:off
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
//		/***** Category 1. ReachSafety *****/
//		/*** Subcategory    ReachSafety-Arrays ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/array-examples/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/array-industry-pattern/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/reducercommutativity/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-BitVectors ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/bitvector/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/bitvector-regression/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/bitvector-loops/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//			
//		/*** Subcategory   ReachSafety-ControlFlow ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ntdrivers-simplified/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ssh-simplified/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/locks/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ntdrivers/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ssh/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		
//		/*** Subcategory   ReachSafety-ReachSafety-ECA ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/eca-rers2012/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/psyco/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		
//		/*** Subcategory   ReachSafety-Heap ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/heap-manipulation/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/list-properties/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ldv-regression/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		// TODO: add ldv-regression/test[0-9][0-9]_false-unreach-call*.c ldv-regression/test[0-9][0-9]_true-unreach-call*.c
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ddv-machzwd/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/forester-heap/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/list-ext-properties/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/list-ext2-properties/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		
//		/*** Subcategory    ReachSafety-Floats ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/floats-cdfpl/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/floats-cbmc-regression/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/float-benchs/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/floats-esbmc-regression/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   ReachSafety-Loops ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loops/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loop-acceleration/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loop-invgen/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loop-lit/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loop-new/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/loop-industry-pattern/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		
//		
//		
//		/***** Category 2. MemSafety *****/
//		/*** Subcategory    MemSafety-Arrays ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/array-memsafety/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/array-examples/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/reducercommutativity/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//
//		/*** Subcategory   MemSafety-Heap ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/memsafety/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/list-ext-properties/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/memory-alloca/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ldv-memsafety/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ldv-memsafety/", new String[]{ ALL_C }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ldv-memsafety-bitfields/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/bitvector-loops/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		
//		/*** Subcategory    MemSafety-LinkedLists ***/
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/heap-manipulation/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/forester-heap/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/list-properties/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),
//		new DirectoryFileEndingsPair("examples/sv-benchmarks/c/ddv-machzwd/", new String[]{ ALL_I }, FILE_OFFSET,  FILES_PER_DIR_LIMIT),

	};
	

	private static final String[] mCurrentBugs = {};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 900 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each setting that is defined here. The path
	 * are defined relative to the folder "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 * 
	 */
	private static final String[] mSettings = { 
			
//			"buchiAutomizer/ncsb/SUNFLOWER-ORIGINAL-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY2-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY3-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/ORIGINAL-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY2-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY3-SAVE-AUT.epf",
			"buchiAutomizer/ncsb/INTSET_LAZY2.epf",
			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY2.epf",
			"buchiAutomizer/ncsb/INTSET_LAZY3.epf",
			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY3.epf",
			"buchiAutomizer/ncsb/ORIGINAL.epf",
			"buchiAutomizer/ncsb/SUNFLOWER-ORIGINAL.epf",
	};

	private static final String[] mCToolchains = {
			// "BuchiAutomizerCInlineWithBlockEncoding.xml",
			"BuchiAutomizerCInline.xml", 
		};

	
    @Override
    public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
            return new SomeVerificationResultTestResultDecider(ultimateRunDefinition);
    }
    
    
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		DirectoryFileEndingsPair[] mPairsToTry=mDirectoryFileEndingsPairs;
		
		
		for (final DirectoryFileEndingsPair dfep : mPairsToTry) {
			for (final String toolchain : mCToolchains) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), mSettings, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}
	// @formatter:on
}

