/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.AbstractModelCheckerTestSuite.DirectoryFileEndingsPair;

/**
 * @author heizmann@informatik.uni-freiburg.de, musab@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Reach_PreciseMemoryModel_HeuristicEvaluation extends
		AbstractTraceAbstractionTestSuite {
	
	private static final DirectoryFileEndingsPair[] m_SVCOMP_Examples = {
		/*** Category 1. Arrays ***/
//		new DirectoryFileEndingsPair("examples/svcomp/array-examples/", new String[]{ ".i" }) ,
		
		/*** Category 2. Bit Vectors ***/
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector/", new String[]{ ".i", ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }) ,
		
		/*** Category 4. Control Flow and Integer Variables ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }) ,
		
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}) ,
		
//		new DirectoryFileEndingsPair("examples/svcomp/eca-rers2012/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }) ,
		
		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }) ,
		
		/*** Category 7. Memory Safety ***/
//		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }) ,

		/*** Category 8. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }) ,
		
		/*** Category 9. Sequentialized Concurrent Programs ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }) ,
	};
	
	private static final String[] m_UltimateRepository = {
		"examples/programs/nonlinearArithmetic",
//		"examples/programs/quantifier",
//		"examples/programs/random",
//		"examples/programs/real-life",
//		"examples/programs/reals",
//		"examples/programs/recursivePrograms",
//		"examples/programs/regression",
//		"examples/programs/scalable",
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
		/*** No Heuristic ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_NotIncrementally.epf",
		/*** Heuristic 1 (OUTSIDE_LOOP_FIRST1) ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic1.epf",
		/*** Heuristic 2 (OUTSIDE_LOOP_FIRST2) ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic2.epf",
		/*** Heuristic 3 (INSIDE_LOOP_FIRST1) ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic3.epf",
		/*** Heuristic 4 (MIX_INSIDE_OUTSIDE) ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic4.epf",
		/*** Heuristic 5 (TERMS_WITH_SMALL_CONSTANTS_FIRST) ***/
		"automizer/ForwardPredicates_SvcompReachPreciseMM_Heuristic5.epf",
	};
	
	// Time out for each test case in milliseconds
	private static long m_Timeout = 60 * 1000;
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (String setting : m_Settings) {
			addTestCases("AutomizerC.xml", 
					setting, 
					m_SVCOMP_Examples,
					m_Timeout);
		}
		
		for (String setting : m_Settings) {
			addTestCases(
					"AutomizerBpl.xml",
					setting,
					m_UltimateRepository,
				    new String[] {".bpl"},
				    m_Timeout);
		}
		for (String setting : m_Settings) {
			addTestCases(
					"AutomizerC.xml",
					setting,
					m_UltimateRepository,
				    new String[] {".c", ".i"},
				    m_Timeout);
		}
		return super.createTestCases();
	}
	
}
