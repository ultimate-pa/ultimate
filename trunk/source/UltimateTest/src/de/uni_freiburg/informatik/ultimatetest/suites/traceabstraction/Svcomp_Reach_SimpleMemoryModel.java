/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractModelCheckerTestSuite.DirectoryFileEndingsPair;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Reach_SimpleMemoryModel extends
		AbstractTraceAbstractionTestSuite {
	
	
	private static int m_FilesPerDirectoryLimit = 5;


	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
		
		/*** Category 5. Device Drivers Linux 64-bit ***/
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 10. Simple  ***/
		/* This category uses in fact the simple memory model, but it is sound to verify it using the precise memory model */
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
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
		"svcomp2015/svComp-64bit-simple-Automizer.epf",
	};
	
	
	private static final String[] m_CToolchains = {
		"AutomizerC.xml",
//		"AutomizerCInline.xml",
	};

	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_SVCOMP_Examples);
			}
		}
		return super.createTestCases();
	}
}
