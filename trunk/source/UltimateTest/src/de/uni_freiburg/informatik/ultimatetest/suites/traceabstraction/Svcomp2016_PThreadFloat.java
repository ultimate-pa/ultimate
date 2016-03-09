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

import de.uni_freiburg.informatik.ultimatetest.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp2016_PThreadFloat extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs_32bit = {
		
		/*** Category 3. Concurrency ***/
		new DirectoryFileEndingsPair("examples/svcomp/pthread/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/pthread-atomic/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/pthread-ext/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/pthread-wmm/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/pthread-lit/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-races/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
			
		/*** Category 11. Floats ***/
		new DirectoryFileEndingsPair("examples/svcomp/floats-cdfpl/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/floats-cbmc-regression/", new String[]{ ".i", }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/float-benchs/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,

	};
	
	
	private static final String[] m_CurrentBugs_32bit = {
		};
	
	
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs_64bit = {
	};
	
	private static final String[] m_CurrentBugs_64bit = {
	};

	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final String[] m_Settings_32bit = {
		"svcomp2016/svcomp-Reach-32bit-Automizer_Default.epf",
	};
	
	private static final String[] m_Settings_64bit = {
		"svcomp2016/svcomp-Reach-64bit-Automizer_Default.epf",
	};

	
	private static final String[] m_CToolchains = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
	};
	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings_32bit) {
			for (String toolchain : m_CToolchains) {
				addTestCase(toolchain, setting, m_DirectoryFileEndingsPairs_32bit);
				addTestCase(toolchain, setting, m_CurrentBugs_32bit, new String[] {".c", ".i"});
			}
		}
		
		for (String setting : m_Settings_64bit) {
			for (String toolchain : m_CToolchains) {
				addTestCase(toolchain, setting, m_DirectoryFileEndingsPairs_64bit);
				addTestCase(toolchain, setting, m_CurrentBugs_64bit, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
