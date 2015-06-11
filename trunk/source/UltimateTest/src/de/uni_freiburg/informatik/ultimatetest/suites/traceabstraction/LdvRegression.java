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
public class LdvRegression extends
		AbstractTraceAbstractionTestSuite {
	
	
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;


	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
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
		"svcomp2015/svComp-64bit-precise-Automizer.epf",
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
