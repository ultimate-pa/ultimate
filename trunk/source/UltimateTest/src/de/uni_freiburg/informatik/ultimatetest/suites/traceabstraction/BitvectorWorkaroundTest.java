/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractModelCheckerTestSuite.DirectoryFileEndingsPair;

/**
 * Test for the bitvector workaround that translates each int into a 32 bit
 * bitvector.
 * @author heizmanninformatik.uni-freiburg.de
 *
 */

public class BitvectorWorkaroundTest extends AbstractTraceAbstractionTestSuite {
	
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
//	private static int m_FilesPerDirectoryLimit = 20;
	
	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
//		/*** Category 1. Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 2. Bit Vectors ***/
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 4. Control Flow and Integer Variables ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 5. Device Drivers Linux 64-bit ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.0/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.4-simple/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.7.3/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-commit-tester/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-consumption/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.12-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-linux-3.16-rc1/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-validator-v0.6/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 7. Memory Safety ***/
//		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//
//		/*** Category 8. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 9. Sequentialized Concurrent Programs ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 10. Simple  ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		
//		/*** Category 12. Termination ***/
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
//		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
	};
	
	
	private static final String[] m_UltimateRepository = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy",
	};
	
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] m_Settings = {
		"automizer/BitvectorWorkaround.epf",
		"svcomp2015/svComp-64bit-precise-Automizer.epf",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 30 * 1000;
	}
	
	private static final String[] m_BoogieToolchains = {
		"AutomizerBpl.xml",
//		"AutomizerBplInline.xml",
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
		
		for (String setting : m_Settings) {
			for (String toolchain : m_BoogieToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".bpl"});
			}
		}
		for (String setting : m_Settings) {
			for (String toolchain : m_CToolchains) {
				addTestCases(toolchain, setting, m_UltimateRepository, 
						new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
