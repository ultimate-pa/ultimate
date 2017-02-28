/*
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.OverapproximatingSafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class InteractiveDevelTestSuite extends AbstractEvalTestSuite {
	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;
	
	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
			//### BPL
//			new Triple<>("../Interactive/toolchains/AutomizerBpl.xml", BPL, "../Interactive/settings/svcomp-Reach-64bit-Automizer_Default.epf"),
//			new Triple<>("../Interactive/toolchains/AutomizerBpl.xml", BPL, "../Interactive/settings/64bit-Automizer_Parrot.epf"),

			//### C
			new Triple<>("../Interactive/toolchains/AutomizerC.xml", C, "../Interactive/settings/svcomp-Reach-64bit-Automizer_Default.epf"),
			new Triple<>("../Interactive/toolchains/AutomizerC.xml", C, "../Interactive/settings/ResetSettingsFixed.epf"),
			new Triple<>("../Interactive/toolchains/AutomizerC.xml", C, "../Interactive/settings/ResetSettingsCamel.epf"),
			new Triple<>("../Interactive/toolchains/AutomizerC.xml", C, "../Interactive/settings/ResetSettingsWolf.epf"),
//			new Triple<>("../Interactive/toolchains/AutomizerC.xml", C, "../Interactive/settings/64bit-Automizer_Parrot.epf"),
	};

	private static final String[] INPUT = new String[] {
//			"examples/Interactive/input/",
			"examples/Interactive/input/square_1_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_8_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_4_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_2_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_3_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_1_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_1_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_4_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_5_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_1_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_7_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_6_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_6_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_8_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_5_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_8_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_2_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_4_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_2_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_5_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_6_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_6_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_8_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_7_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_7_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_4_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_5_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_3_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_6_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_3_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_4_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_2_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/square_1_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_7_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_7_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_2_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_1_3_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_2_5_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_1_true-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/newton_3_8_false-unreach-call.i",
			"/examples/svcomp/floats-cdfpl/sine_3_false-unreach-call.i",
//			"examples/Interactive/input/float12_true-unreach-call.i",

	};
	// @formatter:on
	
	@Override
	protected long getTimeout() {
		// return 90 * 1000 * 1000;
		// return 15 * 1000;
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
				new ColumnDefinition("TraceCheckerStatistics_NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in UnsatCore", null,
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
}