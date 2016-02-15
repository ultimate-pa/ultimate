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
//			new Triple<>("AutomizerBpl.xml", BPL, "EmptySettings.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/AIv2_CON.epf"),
			
			//### C
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationv2C.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationv2C.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationv2C.xml", C, "ai/AIv2_CON.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/Automizer+AIv2_CON.epf"),
	};



	private static final String[] INPUT = new String[] {
			/* ULTIMATE repo */
//			"examples/programs/abstractInterpretation/",
//			"examples/programs/abstractInterpretation/regression",
//			"examples/programs/abstractInterpretation/regression/CountTillBound-Loop-2.bpl",
			"examples/programs/abstractInterpretation/congruence.bpl",
			
			/* BUGS */
			
			// UNSAFE_DEREF / SAFE
//			"examples/svcomp/array-memsafety/add_last_unsafe_false-valid-deref.c",

			// UNSAFE / SAFE
//			"examples/svcomp/bitvector-regression/pointer_extension3_false-unreach-call.c",
			
			// IndexOutOfBoundsException
//			"examples/svcomp/ldv-consumption/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.c",
			
			// NullPointerException (Evaluator)
//			"examples/svcomp/float-benchs/inv_square_true-unreach-call.c",
			
			// Timeout
//			"examples/svcomp/busybox-1.22.0/chroot-incomplete_false-unreach-call.i",
			
			
			///////////////////////////////////////////
			/* SVCOMP */
			//"examples/svcomp",
			
			
//			"examples/svcomp/array-examples",
//			"examples/svcomp/array-memsafety",
//			"examples/svcomp/bitvector",
//			"examples/svcomp/bitvector-loops",
//			"examples/svcomp/bitvector-regression",
//			"examples/svcomp/busybox-1.22.0",
//			"examples/svcomp/ddv-machzwd",
//			"examples/svcomp/eca-rers2012",
//			"examples/svcomp/float-benchs",
//			"examples/svcomp/floats-cbmc-regression",
//			"examples/svcomp/floats-cdfpl",
//			"examples/svcomp/heap-manipulation",
//			"examples/svcomp/ldv-challenges",
//			"examples/svcomp/ldv-commit-tester",
//			"examples/svcomp/ldv-consumption",
//			"examples/svcomp/ldv-linux-3.0",
//			"examples/svcomp/ldv-linux-3.12-rc1",
//			"examples/svcomp/ldv-linux-3.16-rc1",
/*			"examples/svcomp/ldv-linux-3.4-simple",
			"examples/svcomp/ldv-linux-3.7.3",
			"examples/svcomp/ldv-linux-4.2-rc1",
			"examples/svcomp/ldv-memsafety",
			"examples/svcomp/ldv-races",
			"examples/svcomp/ldv-regression",
			"examples/svcomp/ldv-validator-v0.6",
			"examples/svcomp/ldv-validator-v0.8",
			"examples/svcomp/list-ext-properties",
			"examples/svcomp/list-properties",
			"examples/svcomp/locks",
			"examples/svcomp/loop-acceleration",
			"examples/svcomp/loop-invgen",
			"examples/svcomp/loop-lit",
			"examples/svcomp/loop-new",
			"examples/svcomp/loops",
			"examples/svcomp/memory-alloca",
			"examples/svcomp/memory-unsafe",
			"examples/svcomp/memsafety",
			"examples/svcomp/memsafety-ext",
			"examples/svcomp/ntdrivers",
			"examples/svcomp/ntdrivers-simplified",
			"examples/svcomp/product-lines",
			"examples/svcomp/pthread",
			"examples/svcomp/pthread-atomic",
			"examples/svcomp/pthread-ext",
			"examples/svcomp/pthread-lit",
			"examples/svcomp/pthread-wmm",
			"examples/svcomp/recursive",
			"examples/svcomp/recursive-simple",
			"examples/svcomp/reducercommutativity",
			"examples/svcomp/regression",
			"examples/svcomp/seq-mthreaded",
			"examples/svcomp/seq-pthread",
			"examples/svcomp/signedintegeroverflow-regression",
			"examples/svcomp/ssh",
			"examples/svcomp/ssh-simplified",
			"examples/svcomp/systemc",
			"examples/svcomp/termination-15",
			"examples/svcomp/termination-crafted",
			"examples/svcomp/termination-crafted-lit",
			"examples/svcomp/termination-libowfat",
			"examples/svcomp/termination-memory-alloca",
			"examples/svcomp/termination-numeric",
			"examples/svcomp/termination-restricted-15",*/
	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		return 10 * 1000 ;
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
		return new SafetyCheckTestResultDecider(urd, true);
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
