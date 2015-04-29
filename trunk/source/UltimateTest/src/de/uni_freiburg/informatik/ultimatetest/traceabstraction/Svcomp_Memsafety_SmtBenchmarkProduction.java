/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp_Memsafety_SmtBenchmarkProduction extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
		/*** Category 7. Memory Safety ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memsafety-ext/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
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
		"automizer/smtBenchmarkProduction/Z3-mem.epf",
		"automizer/smtBenchmarkProduction/CVC4-mem.epf",
	};


	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			addTestCases("AutomizerCWithBlockEncoding.xml", 
					setting, 
					m_SVCOMP_Examples);
		}
		return super.createTestCases();
	}

	
}
