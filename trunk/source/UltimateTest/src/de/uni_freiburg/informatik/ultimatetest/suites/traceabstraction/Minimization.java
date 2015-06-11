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
public class Minimization extends AbstractTraceAbstractionTestSuite {
	
	
	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = 7;
	
	private static final DirectoryFileEndingsPair[] s_SVCOMP_Programs = {
		/*** Category 1. Arrays ***/
		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 2. Bit Vectors ***/
		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 4. Control Flow and Integer Variables ***/
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}) , // contains "n.c24_false-unreach-call.i", which's test doesn't terminate
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}, m_FilesPerDirectoryLimit) ,
		
		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 7. Memory Safety ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,

		/*** Category 8. Recursive ***/
		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 9. Sequentialized Concurrent Programs ***/
		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		
		/*** Category 10. Simple  ***/
		/* This category uses in fact the simple memory model, but it is sound to verify it using the precise memory model */
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/ssh/", new String[]{ ".c" }, m_FilesPerDirectoryLimit) ,
	};
	
	/**
	 * List of path. Ultimate will be run for each program that you find in
	 * one of there paths.
	 */
	private static final String[] s_UltimateRepository_Programs = {
//		"examples/programs/regression",
//		"examples/programs/quantifier/",
//		"examples/programs/quantifier/regression",
//		"examples/programs/toy",
//		"examples/programs/random",
//		"examples/programs/scaleable",
//		"examples/programs/real-life",
	};
	
	
	/**
	 * List of path to setting files. 
	 * Ultimate will run on each program with each setting that is defined here.
	 * The path are defined relative to the folder "trunk/examples/settings/",
	 * because we assume that all settings files are in this folder.
	 * 
	 */
	private static final String[] s_Settings = {
		"automizer/minimization/TreeInterpolants-DFA_HOPCROFT_ARRAYS.epf",
		"automizer/minimization/TreeInterpolants-MINIMIZE_SEVPA.epf",
		"automizer/minimization/TreeInterpolants-NONE.epf",
		"automizer/minimization/TreeInterpolants-SHRINK_NWA.epf",
	};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : s_Settings) {
			addTestCases("AutomizerCInline.xml", 
					setting, 
					s_SVCOMP_Programs);
		}
		
		for (String setting : s_Settings) {
			addTestCases(
					"AutomizerBplInline.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".bpl"});
		}
		for (String setting : s_Settings) {
			addTestCases(
					"AutomizerCInline.xml",
					setting,
					s_UltimateRepository_Programs,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}

}
