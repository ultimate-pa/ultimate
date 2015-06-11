package de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp_Termination extends AbstractBuchiAutomizerTestSuite {
	
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	
	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {

		/*** Category 12. Termination ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
	};

	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 300 * 1000;
	}
	
	
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"svcomp2015/svComp-64bit-termination-Automizer.epf",
	};
	
	private static final String[] m_CToolchains = {
		"BuchiAutomizerCWithBlockEncoding.xml",
//		"BuchiAutomizerCInlineWithBlockEncoding.xml",
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
