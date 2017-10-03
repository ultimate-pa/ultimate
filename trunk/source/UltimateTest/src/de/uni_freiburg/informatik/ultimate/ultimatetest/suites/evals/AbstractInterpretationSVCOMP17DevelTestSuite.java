/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.OverapproximatingSafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class AbstractInterpretationSVCOMP17DevelTestSuite extends AbstractEvalTestSuite {
	
	private static final String[] C = new String[] { ".i", ".c" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;
	
	private static final String[] DREF_32 = { "svcomp2017/taipan/svcomp-Deref-32bit-Taipan_Bitvector.epf",
			"svcomp2017/taipan/svcomp-Deref-32bit-Taipan_Default.epf",
			"svcomp2017/automizer/svcomp-Deref-32bit-Automizer_Bitvector.epf",
			"svcomp2017/automizer/svcomp-Deref-32bit-Automizer_Default.epf" };
	private static final String[] DREF_FREE_MEMTRACK_32 =
			{ "svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Bitvector.epf",
					"svcomp2017/taipan/svcomp-DerefFreeMemtrack-32bit-Taipan_Default.epf",
					"svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf",
					"svcomp2017/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf" };
	private static final String[] OVERFLOW_32 = { "svcomp2017/taipan/svcomp-Overflow-32bit-Taipan_Default.epf",
			"svcomp2017/automizer/svcomp-Overflow-32bit-Automizer_Default.epf" };
	private static final String[] OVERFLOW_64 = { "svcomp2017/taipan/svcomp-Overflow-64bit-Taipan_Default.epf",
			"svcomp2017/automizer/svcomp-Overflow-64bit-Automizer_Default.epf" };
	private static final String[] REACH_32 = { "svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Bitvector.epf",
			"svcomp2017/taipan/svcomp-Reach-32bit-Taipan_Default.epf",
			"svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf",
			"svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Default.epf" };
	private static final String[] REACH_64 = { "svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Bitvector.epf",
			"svcomp2017/taipan/svcomp-Reach-64bit-Taipan_Default.epf",
			"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Bitvector.epf",
			"svcomp2017/automizer/svcomp-Reach-64bit-Automizer_Default.epf" };
	
	// Toolchain
	private static final Pair<String, String[]> TOOLCHAIN = new Pair<>("AutomizerC.xml", C);
	
	// @formatter:off
	@SuppressWarnings("unchecked")
	private static List<Pair<String, String[]>> getInput() {
		final List<Pair<String, String[]>> input = new ArrayList<>();

		// ******** DREF FREE MEMTRACK ********

		// HeapMemSafety / HeapMemSafety.Merged / ArraysMemSafety
		input.add(new Pair<String, String[]>("examples/svcomp/termination-crafted/Nyala-2lex_false-valid-deref.c", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-1_true-valid-memsafety.i", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/termination-crafted/LexIndexValue-Pointer_false-valid-deref.c", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3.1_true-valid-memsafety.i", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/ldv-memsafety-bitfields/test-bitfields-3_true-valid-memsafety.i", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/termination-crafted/SyntaxSupportPointer01_false-valid-deref.c", DREF_FREE_MEMTRACK_32));

		// ArraysMemSafety.Merged
		input.add(new Pair<String, String[]>("examples/svcomp/termination-crafted/Arrays03-ValueRestictsIndex_false-valid-deref.c", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/termination-crafted/Arrays01-EquivalentConstantIndices_false-valid-deref.c", DREF_FREE_MEMTRACK_32));
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/avg60_false-valid-deref.i", DREF_FREE_MEMTRACK_32));


		// ******** UNREACH CALL 32 Bit ********

		// Floats.Merged / Floats
		input.add(new Pair<String, String[]>("examples/svcomp/floats-esbmc-regression/rounding_functions_true-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/floats-esbmc-regression/modf_true-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/floats-esbmc-regression/nearbyint_true-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/floats-esbmc-regression/rint_true-unreach-call.i", REACH_32));

		// ArraysReach
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/rangesum20_false-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/rangesum05_false-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/rangesum10_false-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/rangesum60_false-unreach-call.i", REACH_32));
		input.add(new Pair<String, String[]>("examples/svcomp/reducercommutativity/rangesum40_false-unreach-call.i", REACH_32));

		return input;
	}


	// @formatter:on

	@Override
	protected long getTimeout() {
		// return 90 * 1000 * 1000;
		// return 90 * 1000;
		return 30 * 1000;
		// return 15 * 60 * 1000;
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
				new ColumnDefinition("traceCheckStatistics_NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
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
		final List<Pair<String, String[]>> input = getInput();

		for (int i = 0; i < input.size(); i++) {
			for (int j = 0; j < input.get(i).getSecond().length; j++) {
				addTestCase(TOOLCHAIN.getFirst(), input.get(i).getSecond()[j], new DirectoryFileEndingsPair[] {
						new DirectoryFileEndingsPair(input.get(i).getFirst(), TOOLCHAIN.getSecond(), DEFAULT_LIMIT) });
			}

		}

		return super.createTestCases();
	}
}
