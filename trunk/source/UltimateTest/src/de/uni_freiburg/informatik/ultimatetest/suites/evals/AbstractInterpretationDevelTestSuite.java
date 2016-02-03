/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.util.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationDevelTestSuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;
	// private static final int DEFAULT_LIMIT = 10;
	// @formatter:off
	
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
			//### BPL 
//			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/AIv2_INT.epf"),			
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/Automizer+AIv2_INT.epf"),
			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "EmptySettings.epf"),
			
			//### C
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
			new Triple<>("AbstractInterpretationv2C.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
			
	};



	private static final String[] INPUT = new String[] {
			/* ULTIMATE repo */
//			 "examples/programs/abstractInterpretation/",
			 "examples/programs/abstractInterpretation/regression",
//			"examples/programs/abstractInterpretation/regression/whileProcedure.bpl",

			// ########### Bugs ###########
			// Here are representatives of current bugs 

			 
			//no exact representable decimal result (106 total) 
			 "examples/svcomp/eca-rers2012/Problem16_label02_true-unreach-call.c",
			 "examples/svcomp/eca-rers2012/Problem16_label00_false-unreach-call.c",
//			 
//			 //NoSuchElementException: No value present: java.util.Optional.get(Optional.java:135) (16 total)
			 "examples/svcomp/recursive-simple/fibo_2calls_10_true-unreach-call.c",
			 "examples/svcomp/recursive-simple/id2_b3_o5_true-unreach-call.c",

//			 //ArrayIndexOutOfBoundsException (all)
			 "examples/svcomp/systemc/transmitter.01_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.02_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.03_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.04_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.05_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.06_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.07_false-unreach-call_false-termination.cil.c",
			 "examples/svcomp/systemc/transmitter.08_false-unreach-call_false-termination.cil.c",
//
//			 //unsoundness (all) 
			 "examples/svcomp/recursive-simple/id_i10_o10_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_i15_o15_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_i20_o20_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_i25_o25_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_o1000_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_o100_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_o10_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_o200_false-unreach-call.c",
			 "examples/svcomp/recursive-simple/id_o20_false-unreach-call.c",
//			 "examples/programs/abstractInterpretation/regression/Collatz.bpl",
//
//			//AStar does not terminate (246 total) 
			"examples/svcomp/locks/test_locks_12_true-unreach-call_false-termination.c",
			"examples/svcomp/locks/test_locks_9_true-unreach-call.c",
			"examples/svcomp/product-lines/email_spec0_product16_false-unreach-call.cil.c",
			"examples/svcomp/product-lines/email_spec4_productSimulator_false-unreach-call.cil.c",
			"examples/svcomp/seq-mthreaded/rekh_nxt_false-unreach-call.1.M1.c",
	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		return 15 * 1000 ;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Total time", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCases(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
