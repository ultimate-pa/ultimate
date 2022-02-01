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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer.AbstractBuchiAutomizerTestSuite;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class TerminationNcsbComparison extends AbstractBuchiAutomizerTestSuite {

	/** Limit the number of files per directory. */

	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;

//	 private static int mFilesPerDirectoryLimit = 1;
	 private static final int FILE_OFFSET = 0;
    private static final boolean runOnlySelectedExample=false;

	// @formatter:off
	private static final String STANDARD_DOT_C_PATTERN = ".*_false-termination.*\\.c|.*_true-termination.*\\.c";
	private static final String STANDARD_DOT_I_PATTERN = ".*_false-termination.*\\.c.i|.*_true-termination.*\\.c.i";
	
	
	private static final String[] NormalCases_product_lines={
			"/elevator_spec14_productSimulator_false-unreach-call_true-termination.cil.c",
			"/elevator_spec1_product03_true-unreach-call_true-termination.cil.c",
			"/elevator_spec2_product18_false-unreach-call_true-termination.cil.c",
			"/elevator_spec2_product19_true-unreach-call_true-termination.cil.c",
			"/elevator_spec2_product20_false-unreach-call_true-termination.cil.c",
			"/elevator_spec2_product27_true-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product11_false-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product27_false-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product28_false-unreach-call_true-termination.cil.c",
			"/elevator_spec9_product26_false-unreach-call_true-termination.cil.c",
			"/elevator_spec9_product32_false-unreach-call_true-termination.cil.c",
			"/email_spec0_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec11_product03_true-unreach-call_true-termination.cil.c",
			"/email_spec11_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec1_product12_true-unreach-call_true-termination.cil.c",
			"/email_spec1_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec27_product13_true-unreach-call_true-termination.cil.c",
			"/email_spec27_product17_false-unreach-call_true-termination.cil.c",
			"/email_spec27_product18_false-unreach-call_true-termination.cil.c",
			"/email_spec27_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec3_product13_false-unreach-call_true-termination.cil.c",
			"/email_spec4_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec6_product12_false-unreach-call_true-termination.cil.c",
			"/email_spec6_product21_false-unreach-call_true-termination.cil.c",
			"/email_spec6_product22_false-unreach-call_true-termination.cil.c",
			"/email_spec6_productSimulator_false-unreach-call_true-termination.cil.c",
			"/email_spec7_product13_true-unreach-call_true-termination.cil.c",
			"/email_spec9_productSimulator_false-unreach-call_true-termination.cil.c",
			"/minepump_spec1_product01_true-unreach-call_false-termination.cil.c"
	}; 
	
	private static final String[] NormalCases_seq_mthreaded={
			"/pals_STARTPALS_Triplicated_false-unreach-call.1.ufo.BOUNDED-10.pals_true-termination.c",
			"/pals_STARTPALS_Triplicated_false-unreach-call.2.ufo.BOUNDED-10.pals_true-termination.c",
	}; 

	private static final String[] NormalCases_systemc={
			"/token_ring.07_false-unreach-call_false-termination.cil.c",
			"/token_ring.07_true-unreach-call_false-termination.cil.c",
			"/toy2_false-unreach-call_false-termination.cil.c",
			"/toy_true-unreach-call_false-termination.cil.c",
	}; 	
	
	private static final String[] NormalCases_locks={
			"/test_locks_10_true-unreach-call_true-valid-memsafety_false-termination.c",
	}; 		

	private static final String[] NormalCases_recursive_simple={
			"/fibo_2calls_4_false-unreach-call_true-termination.c",
			"/fibo_2calls_4_true-unreach-call_true-termination.c",
			"/fibo_2calls_5_false-unreach-call_true-termination.c",
			"/fibo_2calls_5_true-unreach-call_true-termination.c",
			"/fibo_2calls_6_false-unreach-call_true-termination.c",
			"/fibo_2calls_6_true-unreach-call_true-termination.c",
			"/fibo_2calls_8_true-unreach-call_true-termination.c",
			"/fibo_5_false-unreach-call_true-termination.c",
			"/fibo_5_true-unreach-call_true-termination.c",
			"/id2_i5_o5_false-unreach-call_true-termination.c"
	}; 			
	
	private static final String[] NormalCases_recursive={
			"/Addition01_true-unreach-call_true-no-overflow_true-termination.c",
			"/Fibonacci02_true-unreach-call_true-no-overflow_true-termination.c",
			"/McCarthy91_false-unreach-call_true-no-overflow_true-termination.c",
			"/McCarthy91_true-unreach-call_true-no-overflow_true-termination.c",
			"/recHanoi02_true-unreach-call_true-no-overflow_true-termination.c"
	}; 				
	private static final String[] NormalCases_termination_crafted_lit_todo={
			"/AliasDarteFeautrierGonnord-SAS2010-Fig2b_true-termination.c",
			"/GulwaniJainKoskinen-PLDI2009-Fig1_true-termination.c",
			"/LeeJonesBen-Amram-POPL2001-Ex3_true-termination.c",
			"/PodelskiRybalchenko-LICS2004-Fig2-TACAS2011-Fig3_true-termination.c",
			"/joey_false-termination.c"
	};
	
	private static final String[] NormalCases_termination_crafted={
			"/4BitCounterPointer_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/McCarthy91_Recursion_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/MutualRecursion_1a_true-no-overflow_false-termination_true-valid-memsafety.c",
			"/NestedRecursion_1b_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/NestedRecursion_1c_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/NestedRecursion_1d_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/NestedRecursion_2c_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/TelAviv-Amir-Minimum_true-no-overflow_true-termination_true-valid-memsafety.c"
	}; 	
	private static final String[] NormalCases_termination_15={
			"/count_up_alloca_true-termination.c.i",
	}; 	
	
	private static final String[] NormalCases_numeric_todo={
			"/Et4_true_true-termination.c",
			"/MultCommutative_true-termination.c"
	};
	private static final String[] NormalCases_numeric={
			"/Binomial_true-termination_false-no-overflow.c",
			"/EvenOdd01_true-termination_true-no-overflow.c",
			"/LeUserDefRec_true-termination_true-no-overflow.c",
			"/Parts_true-termination_true-no-overflow.c",
			"/TerminatorRec02_true-termination_false-no-overflow.c"
	}; 			
	
	private static final String[] NormalCases_termination_restricted_15_todo={
			"/ComplxStruc_false-no-overflow_false-termination.c"
	}; 		
	private static final String[] NormalCases_termination_restricted_15={
			"/UpAndDown_false-termination_true-no-overflow.c",
			"/WhileDecr_true-termination_true-no-overflow.c"
	}; 	
	
	private static final String[] NormalCases_termination_memory_alloca={
			"/BrockschmidtCookFuhs-2013CAV-Fig1-alloca_true-termination.c.i",
			"/CookSeeZuleger-2013TACAS-Fig3-alloca_true-termination.c.i",
			"/CookSeeZuleger-2013TACAS-Fig7b-alloca_true-termination.c.i",
			"/Urban-alloca_true-termination.c.i",
			"/a.06-alloca_true-termination_true-no-overflow.c.i",
			"/a.07-alloca_true-termination_true-no-overflow.c.i",
			"/aviad_true-alloca_true-termination.c.i",
			"/c.01-no-inv-alloca_true-termination_true-no-overflow.c.i",
			"/c.01_assume-alloca_true-termination_true-no-overflow.c.i",
			"/c.03-alloca_true-termination_true-no-overflow.c.i",
			"/c.08-alloca_true-termination_true-no-overflow.c.i",
			"/count_down-alloca_true-termination.c.i",
			"/cstrcat-alloca_true-termination.c.i",
			"/lis-alloca_true-termination.c.i"
	}; 	
	private static final String[] DifficultCases_termination_memory_alloca={
			"/Masse-alloca_true-termination.c.i",
			"/TelAviv-Amir-Minimum-alloca_true-termination.c.i",
			"/Urban-2013WST-Fig2-modified1000-alloca_true-termination.c.i",
			"/ex2-alloca_true-termination.c.i",
			"/ex3a-alloca_true-termination_true-no-overflow.c.i",
			"/ex3b-alloca_true-termination.c.i",
			"/fermat-alloca_true-termination.c.i",
			"/java_Sequence-alloca_true-termination.c.i"
	};
	
	private static final String[] DifficultCases_product_lines={
			"/elevator_spec14_product11_true-unreach-call_true-termination.cil.c",
			"/elevator_spec14_product23_true-unreach-call_true-termination.cil.c",
			"/elevator_spec1_product23_true-unreach-call_true-termination.cil.c",
			"/elevator_spec2_product11_true-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product03_false-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product21_true-unreach-call_true-termination.cil.c",
			"/elevator_spec3_product31_false-unreach-call_true-termination.cil.c",
			"/elevator_spec9_product11_true-unreach-call_true-termination.cil.c",
			"/elevator_spec9_product31_true-unreach-call_true-termination.cil.c"
	};
	
	private static final String[] DifficultCases_seq_mthreaded={
			"/pals_lcr.7_false-unreach-call.1.ufo.BOUNDED-14.pals_true-termination.c",
			"/pals_lcr.7_true-unreach-call.ufo.BOUNDED-14.pals_true-termination.c",
			"/pals_lcr.8_false-unreach-call.1.ufo.BOUNDED-16.pals_true-termination.c",
			"/pals_lcr.8_true-unreach-call.ufo.BOUNDED-16.pals_true-termination.c"
	};	
	
	private static final String[] DifficultCases_systemc={
			"/token_ring.10_false-unreach-call_false-termination.cil.c",
			"/token_ring.10_true-unreach-call_false-termination.cil.c",
			"/token_ring.15_false-unreach-call_false-termination.cil.c",
			"/transmitter.10_false-unreach-call_false-termination.cil.c",
			"/transmitter.12_false-unreach-call_false-termination.cil.c",
			"/transmitter.15_false-unreach-call_false-termination.cil.c",
	};	
	
	private static final String[] DifficultCases_recursive={
			"/Ackermann02_false-unreach-call_true-no-overflow_true-termination.c",
			"/Fibonacci03_true-unreach-call_true-no-overflow_true-termination.c",
			"/Fibonacci04_false-unreach-call_true-no-overflow_true-termination.c",
			"/Fibonacci05_false-unreach-call_true-no-overflow_true-termination.c",
			"/recHanoi01_true-unreach-call_true-no-overflow_true-termination.c",
	};	
	
	private static final String[] DifficultCases_termination_crafted_lit_todo={
			"/ChenFlurMukhopadhyay-SAS2012-Ex2.11_false-termination.c",
			"/HeizmannHoenickeLeikePodelski-ATVA2013-Fig2_true-termination.c",
			"/HeizmannHoenickeLeikePodelski-ATVA2013-Fig8_true-termination.c",
			"/HeizmannHoenickeLeikePodelski-ATVA2013-Fig9_true-termination.c",
			"/LeikeHeizmann-WST2014-Ex5_false-termination.c",
			"/PodelskiRybalchenko-LICS2004-Fig2_true-termination.c",
			"/PodelskiRybalchenko-TACAS2011-Fig3_true-termination.c"
	};		
	private static final String[] DifficultCases_termination_crafted_lit={
			"/HeizmannHoenickeLeikePodelski-ATVA2013-Fig5_true-termination_true-no-overflow.c",
			"/LeeJonesBen-Amram-POPL2001-Ex5_true-termination_true-no-overflow.c",
			"/Urban-WST2013-Fig2-modified1000_true-termination_true-no-overflow.c"
	};	
	
	private static final String[] DifficultCases_termination_crafted_todo={
			"/Hanoi_plus_false-termination_true-valid-memsafety.c",
	};
	
	private static final String[] DifficultCases_termination_crafted={
			"/Ackermann_true-termination_true-valid-memsafety.c",
			"/Arrays01-EquivalentConstantIndices_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/Arrays03-ValueRestictsIndex_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/Copenhagen_disj_true-termination_true-valid-memsafety.c",
			"/Gothenburg_v2_true-termination_true-valid-memsafety.c",
			"/LexIndexValue-Array_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/LexIndexValue-Pointer_true-termination_true-valid-memsafety.c",
			"/MutualRecursion_1b_true-no-overflow_true-termination_true-valid-memsafety.c",
			"/Mysore_false-termination_true-valid-memsafety.c"
	};		
	
	private static final String[] DifficultCases_termination_15={
			"/array12_alloca_true-termination.c.i",
			"/array13_alloca_true-termination.c.i",
			"/array17_alloca_true-termination.c.i",
	};		
	
	private static final String[] DifficultCases_termination_numeric={
			"/Ackermann01_true-termination_true-no-overflow.c",
			"/Fibonacci01_true-termination_true-no-overflow.c"
	};		
	
	private static final String[] DifficultCases_restricted_15_todo={
			"/ChooseLife_false-no-overflow_false-termination.c",
			"/ComplInterv_false-no-overflow_false-termination.c",
			"/DoubleNeg_false-no-overflow_false-termination.c",
			"/Factorial_false-no-overflow_false-termination.c",
			"/Fibonacci_false-no-overflow_false-termination.c",
			"/LogMult_false-no-overflow_true-termination.c",
			"/MirrorInterv_false-no-overflow_false-termination.c"
	};		
	
	private static final String[] DifficultCases_restricted_15={
			"/NO_24_false-termination_true-no-overflow.c",
			"/Swingers_false-termination_true-no-overflow.c"
	};		
	private static final String[] DifficultCases_libowfat={
			"/basename_true-termination.c.i",
			"/dirname_true-termination.c.i",
			"/skip_to_true-termination.c.i",
			"/strpbrk_true-termination.c.i",
	};		
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairsForSelectedCases = {
			new DirectoryFileEndingsPair("examples/svcomp/product-lines/", NormalCases_product_lines, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", NormalCases_seq_mthreaded, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/systemc/", NormalCases_systemc, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/locks/", NormalCases_locks, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", NormalCases_recursive_simple, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/recursive/", NormalCases_recursive, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit-todo/", NormalCases_termination_crafted_lit_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", NormalCases_termination_crafted, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-15/", NormalCases_termination_15, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-numeric-todo/", NormalCases_numeric_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", NormalCases_numeric, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15-todo/", NormalCases_termination_restricted_15_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", NormalCases_termination_restricted_15, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", NormalCases_termination_memory_alloca, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", DifficultCases_seq_mthreaded, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/product-lines/", DifficultCases_product_lines, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/systemc/", DifficultCases_systemc, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", DifficultCases_termination_memory_alloca, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/recursive/", DifficultCases_recursive, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit-todo/", DifficultCases_termination_crafted_lit_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", DifficultCases_termination_crafted_lit, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-todo/", DifficultCases_termination_crafted_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", DifficultCases_termination_crafted, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-15/", DifficultCases_termination_15, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", DifficultCases_termination_numeric, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15-todo/", DifficultCases_restricted_15_todo, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", DifficultCases_restricted_15, FILE_OFFSET, mFilesPerDirectoryLimit),
			new DirectoryFileEndingsPair("examples/svcomp/termination-libowfat/", DifficultCases_libowfat, FILE_OFFSET, mFilesPerDirectoryLimit),			
	};
	
	private static final DirectoryFileEndingsPair[] mDirectoryFileEndingsPairs = {
		/***** Category 5. Termination *****/
		/*** Subcategory  Termination-MainControlFlow ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-crafted-lit-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-numeric-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-restricted-15-todo/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		
		
		/*** Subcategory  Termination-MainHeap ***/
		new DirectoryFileEndingsPair("examples/svcomp/termination-libowfat/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-alloca/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-memory-linkedlists/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-15/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/termination-recursive-malloc/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),

		/*** Subcategory  Termination-Other ***/
		new DirectoryFileEndingsPair("examples/svcomp/pthread-atomic/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/ntdrivers-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/ssh-simplified/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/locks/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/loops/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/loop-acceleration/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/loop-invgen/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/loop-lit/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/loop-new/", new String[]{ STANDARD_DOT_I_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/product-lines/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/recursive/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/recursive-simple/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/systemc/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
		new DirectoryFileEndingsPair("examples/svcomp/seq-mthreaded/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit),
};
	

	private static final String[] mCurrentBugs = {};
	private static final DirectoryFileEndingsPair[] mDirectoryBugPairs = { 
			new DirectoryFileEndingsPair("examples/svcomp/test/", new String[]{ STANDARD_DOT_C_PATTERN }, FILE_OFFSET, mFilesPerDirectoryLimit)
			};
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
//		return Integer.MAX_VALUE;
		return 900 * 1000;
	}

	/**
	 * List of path to setting files. Ultimate will run on each program with each setting that is defined here. The path
	 * are defined relative to the folder "trunk/examples/settings/", because we assume that all settings files are in
	 * this folder.
	 * 
	 */
	private static final String[] mSettings = { 
			
//			"buchiAutomizer/ncsb/SUNFLOWER-ORIGINAL-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY2-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY3-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/ORIGINAL-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY2-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY3-SAVE-AUT.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY2.epf",
//			"buchiAutomizer/ncsb/INTSET_LAZY3.epf",
//			"buchiAutomizer/ncsb/INTSET.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY2.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY3.epf",
			"buchiAutomizer/ncsb/INTSET_GBA.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_GBA.epf",
			"buchiAutomizer/ncsb/INTSET_GBA_ANTICHAIN.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_GBA_ANTICHAIN.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-INTSET_LAZY3.epf",
//			"buchiAutomizer/ncsb/ORIGINAL.epf",
//			"buchiAutomizer/ncsb/SUNFLOWER-ORIGINAL.epf", //
			"buchiAutomizer/ncsb/A-ORIGINAL.epf", // svcomp
//			"buchiAutomizer/ncsb/ROSE-ORIGINAL.epf", //FA, NBA
//			"buchiAutomizer/ncsb/DAISY-ORIGINAL.epf", //CAV 14
	};

	private static final String[] mCToolchains = {
			"BuchiAutomizerCInlineWithBlockEncoding.xml",
//			"BuchiAutomizerCInline.xml", 
		};

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		int mNumberOfMachines = 1;
		int mCurrentMachineNumber = 0;
		
		try(BufferedReader br = new BufferedReader(new FileReader("machine.conf"))) {
		    String line = br.readLine();
		    mNumberOfMachines = Integer.parseInt(line.substring(0, line.indexOf(' ')));
		    line = br.readLine();
		    mCurrentMachineNumber = Integer.parseInt(line.substring(0, line.indexOf(' ')));

		} catch (Exception e) {
			//use single machine
			mNumberOfMachines = 1;
			mCurrentMachineNumber = 0;
		}
		
		File infoFile = new File("Info.log");
		if(infoFile.exists()) {
			infoFile.delete();
		}
		
		DirectoryFileEndingsPair[] mPairsToTry=mDirectoryFileEndingsPairs;
		if(runOnlySelectedExample){
			mPairsToTry=mDirectoryFileEndingsPairsForSelectedCases;
		}
//	    mPairsToTry = mDirectoryBugPairs;
		for (final DirectoryFileEndingsPair dfep : mPairsToTry) {
			for (final String toolchain : mCToolchains) {
					addTestCase(UltimateRunDefinitionGenerator.getRunDefinitionsFromTrunkRegex(
						new String[] { dfep.getDirectory() }, dfep.getFileEndings(), mSettings, toolchain, getTimeout(),
						dfep.getOffset(), dfep.getLimit()));
			}
		}
		return super.createTestCasesMultipleMachine(mNumberOfMachines,mCurrentMachineNumber,mSettings.length);
	}
	// @formatter:on
}

