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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoErrorAndTimeoutTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class IsEmptyHeuristicDevelTestsuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
			new Triple<>("AutomizerC.xml", C, "heuristics/AutomizerC_Reach_32bit_Default_ZeroHeuristic.epf"),

	};

	private static final String[] INPUT = new String[] {
			"examples/programs/heuristics/regression/bug01_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug02_isEmptyHeuristic_recursion.c",
			"examples/programs/heuristics/regression/bug03_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug04_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug05_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug06_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug07_IsEmptyHeuristic.c",
			"examples/programs/heuristics/regression/bug08_IsEmptyHeuristic.c",
			"examples/svcomp/recursive/recHanoi03-2.c", "examples/svcomp/recursive-simple/afterrec-1.c",
			"examples/svcomp/array-examples/sanfoundry_43_ground.i",
			"examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_ok_nondet_linux-43_1a-drivers--net--phy--icplus.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.i",
			"examples/svcomp/ldv-linux-3.4-simple/43_1a_cilled_ok_nondet_linux-43_1a-drivers--hid--hid-kensington.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out.i",
			"examples/svcomp/ldv-commit-tester/main3_arch-x86-oprofile-oprofile-ko--131_1a--79db8ef-1.i",
			"examples/svcomp/ldv-regression/rule57_ebda_blast.c_1.i",
			// "examples/svcomp/ldv-linux-3.0/usb_urb-drivers-input-tablet-kbtab.ko.cil.out.i",

	};

	@Override
	protected long getTimeout() {
		// timeout in ms
		return 900 * 1000;
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		// boolean param decides whether timeouts/unknowns are fails (false) or success (true)
		return new NoErrorAndTimeoutTestResultDecider(urd);
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

	private IUltimateServiceProvider overwriteSettings(final IUltimateServiceProvider oldServices) {
		// --traceabstraction.use.heuristic.emptiness.check true
		// --traceabstraction.scoring.method.to.use.during.heuristic.emptiness.check ZERO

		final String pluginId =
				de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator.PLUGIN_ID;

		final IUltimateServiceProvider overlay = oldServices.registerPreferenceLayer(getClass(), pluginId);
		final IPreferenceProvider prefProvider = overlay.getPreferenceProvider(pluginId);
		prefProvider.put(TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK, true);
		prefProvider.put(TraceAbstractionPreferenceInitializer.LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC, "ZERO");
		return overlay;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs, this::overwriteSettings);
		}
		return super.createTestCases();
	}
}
