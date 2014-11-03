/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.buchiautomizer;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp_Termination extends AbstractBuchiAutomizerTestSuite {
	private static final DirectoryFileEndingsPair[] m_DirectoryFileEndingsPairs = {

//		/*** Category ??? ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/bitvector-regression/", new String[]{ ".i", ".c" }) ,
//		
//		/*** Category 4. Control Flow and Integer Variables ***/
//		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{".c" }) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{".i"}) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{".i"}) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ ".i", ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{".i"}) ,
//		
//		new DirectoryFileEndingsPair("examples/svcomp/eca/", new String[]{".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{".c" }) ,
//		
//		/*** Category 6. Heap Manipulation / Dynamic Data Structures ***/
//		new DirectoryFileEndingsPair("examples/svcomp/heap-manipulation/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/list-properties/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ldv-regression/", new String[]{ ".i" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/ddv-machzwd/", new String[]{ ".i" }) ,
//
//		/*** Category 8. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ ".c" }) ,
//		
//		/*** Category 9. Recursive ***/
//		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ ".c" }) ,
//		new DirectoryFileEndingsPair("examples/svcomp/seq-pthread/", new String[]{ ".i" }) ,
	};

	// Time out for each test case in milliseconds
	private static long m_Timeout = 20 * 1000;

	private static final boolean s_UseTasimp = true;
	private static final String s_TasimpSetting = "buchiAutomizer/staged300Forward-Z3-Tasimp.epf";
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_UseTasimp) {
			addTestCases("BuchiAutomizerCWithBlockEncoding.xml", 
					s_TasimpSetting, 
					m_DirectoryFileEndingsPairs,
					m_Timeout);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
