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
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer.AbstractBuchiAutomizerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp17FoldersAutomizerTermination extends AbstractBuchiAutomizerTestSuite {

	/** Limit the number of files per directory. */
//	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	 private static int mFilesPerDirectoryLimit = 1;
	 private static final int FILE_OFFSET = 10;

	// @formatter:off
	private static final String STANDARD_DOT_C_PATTERN = ".*_false-termination.*\\.c|.*_true-termination.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-termination.*\\.c.i|.*_true-termination.*\\.c.i";
	
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
		/***** Category 5. Termination *****/
		/*** Subcategory  Termination-MainControlFlow ***/
		new DirectoryFileEndingsPair("examples/svcomp/c/locks/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		
//		
//		/*** Subcategory  Termination-MainHeap ***/
//		new DirectoryFileEndingsPair("examples/svcomp/termination-libowfat/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-linkedlists/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-15/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/termination-recursive-malloc/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//
//		/*** Subcategory  Termination-Other ***/
//		new DirectoryFileEndingsPair("examples/svcomp/pthread-atomic/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
};
	

	private static final String[] mCurrentBugs = {};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each setting that is defined here. The path
	 * are defined relative to the folder "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 * 
	 */
	private static final String[] mSettings = { 
			"svcomp2017/automizer/svcomp-Termination-32bit-Automizer_Default.epf",
			"buchiAutomizer/svcomp-Termination-32bit-Automizer_Default-LazyNcsb.epf"
			
//			"buchiAutomizer/biaConstructionStrategy/svcomp-Termination-64bit-Automizer_Default-ASTER.epf",
//			"buchiAutomizer/biaConstructionStrategy/svcomp-Termination-64bit-Automizer_Default-DANDELION.epf",
//			"buchiAutomizer/biaConstructionStrategy/svcomp-Termination-64bit-Automizer_Default-SUNFLOWER.epf",
			
			// "buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_GntaZero.epf",
			// "buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_DefaultBarcelogic.epf",
			// "buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_Default.epf",
	};

	private static final String[] mCToolchains = {
			// "BuchiAutomizerCInlineWithBlockEncoding.xml",
			"BuchiAutomizerCInline.xml", 
		};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		int n = 0;
		for (final DirectoryFileEndingsPair dfep : mDirectoryFileEndingsPairs) {
			n ++;
			if(n > 10) break;
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

