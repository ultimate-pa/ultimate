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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.OverapproximatingSafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("unused")
public class AbstractInterpretationDevelTestSuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
			//### BPL
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_total.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug_noPredAbs.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug_refineAlways.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple.epf"),

			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_P1_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_WO_CON_Debug.epf"),


			//### BPL Inline
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),


			//### C
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),


//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),


			//### C Inline
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
	};



	private static final String[] INPUT = new String[] {
			/* ULTIMATE repo */
//			"examples/programs/abstractInterpretation/congruence.bpl",
			"examples/programs/abstractInterpretation/regression",
//			"examples/programs/abstractInterpretation/regression/all",
//			"examples/programs/abstractInterpretation/regression/all/procedure-Call-bools.bpl",
//			"examples/programs/abstractInterpretation/regression/all/loop-nested-unsafe.bpl",
//			"examples/programs/abstractInterpretation/regression/globals-easy-1-safe.bpl",
//			"examples/programs/abstractInterpretation/regression/all/loop-110517_Martin01.bpl",
//			"examples/programs/abstractInterpretation/regression/loop-procedure.bpl",

//			"examples/programs/abstractInterpretation/regression/all/recursive-CallABAB_incorrect.bpl",
//			"examples/programs/abstractInterpretation/regression/bla.bpl",
//			"examples/programs/abstractInterpretation/regression/modulo-assume-bug-npe.bpl",
//			"examples/programs/abstractInterpretation/regression/division-zero-1.bpl",
//			"examples/programs/abstractInterpretation/regression/division-inequality-bug.bpl",
//			"examples/programs/abstractInterpretation/regression/division-inequality-bug-2.bpl",
//			"examples/programs/abstractInterpretation/regression/modulo-assume-bug.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-CallABAB.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-Collatz.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-CallABAB_count.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-CallABAB_count_incorrect.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-easy-4.bpl",
//			"examples/programs/abstractInterpretation/regression/varupdate-multiplication.bpl",
//			"examples/programs/abstractInterpretation/regression/recursive-CallABAB_simple_incorrect.bpl",

//			"examples/programs/abstractInterpretation/regression/unary-minus-bug.bpl",
//			"examples/programs/abstractInterpretation/regression/loop-CountTillBound-2.bpl",
//			"examples/programs/abstractInterpretation/regression/loop-nested-assume-safe.bpl",
//			"examples/programs/abstractInterpretation/regression/loop-procedure.bpl",
//			"examples/programs/abstractInterpretation/regression/procedure-Loops.bpl",
//			"examples/svcomp/ntdrivers-simplified/floppy_simpl4_true-unreach-call_true-termination.cil.c"
//			"examples/svcomp/bitvector-loops/overflow_false-unreach-call1.i",
//			"examples/svcomp/bitvector-loops/diamond_false-unreach-call2.i",
//			"examples/svcomp/product-lines/email_spec11_productSimulator_false-unreach-call.cil.c",
//			"examples/svcomp/product-lines/email_spec4_product32_false-unreach-call.cil.c",
//			"examples/svcomp/loop-invgen/down_true-unreach-call.i",
//			"examples/svcomp/loop-invgen/",
//			"examples/svcomp/loops/",
//			"examples/svcomp/loop-lit/",
//			"examples/svcomp/loop-new/",
//			"examples/svcomp/loop-acceleration/",
//			"examples/svcomp/loop-new/nested_true-unreach-call.i",
//			"examples/svcomp/loop-lit/css2003_true-unreach-call.c.i",
//			"examples/svcomp/loop-invgen/string_concat-noarr_true-unreach-call.i",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCake01.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCake01HardcodedInput.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCake01InvariantCheck.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCakeWithJohoFractions01.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCakeWithJohoFractions01FixedInput.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCakeWithJohoFractions01HardcodedInput.bpl",
//			"examples/programs/toy/tooDifficultLoopInvariant/GasCakeWithJohoFractions01InvariantCheck.bpl",
	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		// return 30 * 1000 * 1000;
		return 90 * 1000;
		// return 60 * 1000 * 10;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
			new ColumnDefinition(
					"Runtime (ns)", "Avg. runtime",
					ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
			new ColumnDefinition(
					"Allocated memory end (bytes)", "Memory",
					ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
			new ColumnDefinition(
					"Overall iterations", "Iter{-}ations",
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"Abstract Interpretation iterations", "AI Iter{-}ations",
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"AbstractInterpretationStrong", "AI Strong",
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"Abstract Interpretation Time", "AI Avg. Time",
					ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
			new ColumnDefinition(
					"Overall time", "Trace Abstraction Time",
					ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
			new ColumnDefinition(
					"NumberOfCodeBlocks", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"SizeOfPredicatesFP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"SizeOfPredicatesBP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"Conjuncts in SSA", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"Conjuncts in UnsatCore", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"ICC %", "ICC",
					ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),
		};
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new OverapproximatingSafetyCheckTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
