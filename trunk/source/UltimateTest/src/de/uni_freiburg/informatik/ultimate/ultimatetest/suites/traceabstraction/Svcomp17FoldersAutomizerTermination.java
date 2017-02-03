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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer.AbstractBuchiAutomizerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp17FoldersAutomizerTermination extends AbstractBuchiAutomizerTestSuite {

	/** Limit the number of files per directory. */
	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
//	private static int mFilesPerDirectoryLimit = 5;
	
	// @formatter:off
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
		/***** Category 5. Termination *****/
		/*** Subcategory  Termination-MainControlFlow ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".*_false-termination.*\\.c", ".*_true-termination.*\\.c" }, mFilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/termination-15/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-libowfat/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", new String[]{ ".c" }, mFilesPerDirectoryLimit) ,
	};
	// @formatter:on
	
	
	private static final String[] mCurrentBugs = {
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 180 * 1000;
	}

	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] mSettings = {
		"svcomp2016/svcomp-Termination-64bit-Automizer_Default.epf",
//		"buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_GntaZero.epf",
//		"buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_DefaultBarcelogic.epf",
//		"buchiAutomizer/gnta/svcomp-Termination-64bit-Automizer_Default.epf",
	};
	
	
	private static final String[] mCToolchains = {
		"BuchiAutomizerCInlineWithBlockEncoding.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final DirectoryFileEndingsPair dfep : mDirectoryFileEndingsPairs) {
			for (final String toolchain : mCToolchains) {
				addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[]{dfep.getDirectory()}, dfep.getFileEndings(), mSettings, 
						toolchain, dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCases();
	}

	
}
