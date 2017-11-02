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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.benchexec.BenchexecRundefinitionGeneratorPreLog;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.OverapproximatingSafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.reporting.IPreTestLog;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class AbstractInterpretationDevelTestSuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
			//### BPL
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_P1.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_total.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_P1_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug_noPredAbs.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug_refineAlways.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Taipan_Default.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Taipan_Default_Debug.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-Taipan_INT.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-RubberTaipan_Default.epf"),


//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_P1.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_FUTURE_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_P1_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Debug.epf"),
			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_EQ_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple_Debug.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_WO_CON_Debug.epf"),

			//### BPL Inline
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Taipan_Default.epf"),
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-Taipan_Default_Debug.epf"),
//			new Triple<>("AutomizerBplInline.xml", BPL, "ai/svcomp-Reach-32bit-RubberTaipan_Default.epf"),
//			new Triple<>("AutomizerBpl.xml", BPL, "ai/svcomp-Reach-32bit-RubberTaipan_Default.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple_Debug.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),

			//### C
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_total.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_total_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_SMTInterpol.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_total.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug_noPredAbs.epf"),
//			new Triple<>("AutomizerC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Simple_total.epf"),
//			new Triple<>("AutomizerC.xml", C, "svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerC.xml", C, "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf"),


//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
//			new Triple<>("AbstractInterpretationC.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
			new Triple<>("AbstractInterpretationC.xml", C, "ai/eq-bench/svcomp-Reach-32bit-Automizer_Taipan+AI_EQ.epf"),

			//### Regression
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_EQ.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT_Debug.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_COMP_Debug.epf"),
			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),
//			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_CON_Debug.epf"),
			new Triple<>("AbstractInterpretationInline.xml", BPL, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_EQ_Debug.epf"),




			//### C Inline
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Automizer_Default+AIv2_OCT_Debug.epf"),

//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Taipan_Default.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-RubberTaipan_Default.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-LazyTaipan_Default.epf"),
//			new Triple<>("AutomizerCInline.xml", C, "ai/svcomp-Reach-32bit-Taipan_Default_Debug.epf"),

			//EQ Domain
			new Triple<>("AutomizerC.xml", C, "ai/eq-bench/svcomp-Reach-32bit-Automizer_Taipan+AI_EQ.epf"),
	};

	private static final String[] INPUT = new String[] {
			// Normal regressions
//			"examples/programs/abstractInterpretation/regression",
//			"examples/programs/abstractInterpretation/regression/open/int/stmt-bool-true-assign-top.bpl",
//			"examples/programs/abstractInterpretation/regression/non_con/loop-literal-widening-predicate-weakening.bpl",

			//old vars support
//			"examples/programs/abstractInterpretation/bug-old-stmt-3.bpl",
//			"examples/programs/abstractInterpretation/bug-old-stmt-4.bpl",
//			"examples/programs/abstractInterpretation/regression/open/eq/mixedGlobalLocalSelectNonModifyingProcedure.bpl",
//			"examples/svcomp/bitvector-loops/verisec_sendmail__tTflag_arr_one_loop_false-unreach-call.i",
//			"examples/svcomp/loop-acceleration/simple_true-unreach-call4.i",
//			"examples/svcomp/reducercommutativity/rangesum05_false-unreach-call.i",
			"examples/svcomp/loop-new/count_by_k_true-unreach-call_true-termination.i"

	};
	// @formatter:on

	@Override
	protected long getTimeout() {
		// return 90 * 1000 * 1000;
		// return 15 * 60 * 1000;
		// return 5 * 60 * 1000;
		// return 3 * 60 * 1000;
		return 90 * 1000;
		// return 30 * 1000;
		// return 15 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Avg. runtime", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallIterations.toString(), "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntIterations.toString(), "AI Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntStrong.toString(), "AI Strong",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntTime.toString(), "AI Avg. Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Trace Abstraction Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_NumberOfCodeBlocks", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesFP", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesBP", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantCoveringCapability", "ICC", ConversionContext.Percent(true, 2),
						Aggregate.Ignore, Aggregate.Average), };
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

	@Override
	protected IPreTestLog[] constructPreTestLogs() {
		return new IPreTestLog[] { new BenchexecRundefinitionGeneratorPreLog(getClass()) };
	}
}
