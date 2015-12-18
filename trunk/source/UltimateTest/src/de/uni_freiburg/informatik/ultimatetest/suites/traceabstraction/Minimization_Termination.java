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

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer.AbstractBuchiAutomizerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Minimization_Termination extends AbstractBuchiAutomizerTestSuite {

	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
//	private static int m_FilesPerDirectoryLimit = 10;
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs = {
		/*** Category 6. Termination ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-libowfat/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-15/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
	};
	
	
	private static final String[] m_CurrentBugs = {
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"buchiAutomizer/minimization/Delayed.epf",
		"buchiAutomizer/minimization/FairWithSCC.epf",
		"buchiAutomizer/minimization/FairWithoutSCC.epf",
		"buchiAutomizer/minimization/FairDirect.epf",
		"buchiAutomizer/minimization/MinimzeSevpa.epf",
		"buchiAutomizer/minimization/None.epf",
		"buchiAutomizer/minimization/ShrinkNwa.epf",
	};
	
	
	
	private static final String[] m_CToolchains = {
		"BuchiAutomizerCInlineWithBlockEncoding.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_DirectoryFileEndingsPairs);
				addTestCases(toolchain, setting, m_CurrentBugs, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
