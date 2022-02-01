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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogCsv;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals.InterpolationTestSuite;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.GraphSizeCsvProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class AbstractEvalTestSuite extends AbstractModelCheckerTestSuiteWithIncrementalLog {

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, false);
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = getBenchmarks();
		final List<IIncrementalLog> incLogs = new ArrayList<>();
		incLogs.add(getIncrementalLogWithVMParameters());
		incLogs.add(new IncrementalLogWithBenchmarkResults(getClass()));
		benchmarks.stream().map(a -> new IncrementalLogCsv(getClass(), a)).forEach(incLogs::add);
		return incLogs.toArray(new IIncrementalLog[incLogs.size()]);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {

		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = getBenchmarks();
		final ColumnDefinition[] columnDef = getColumnDefinitions();

		final List<ITestSummary> rtr = new ArrayList<>();
		rtr.add(new LatexOverviewSummary(getClass(), benchmarks, columnDef));
		rtr.add(new LatexDetailedSummary(getClass(), benchmarks, columnDef));
		rtr.add(new TraceAbstractionTestSummary(getClass()));
		rtr.add(new CsvSummary(getClass(), benchmarks, columnDef));
		rtr.add(new HTMLSummary(getClass(), benchmarks, columnDef));
		rtr.add(new KingOfTheHillSummary(this.getClass()));
		rtr.add(new StandingsSummary(this.getClass()));
		benchmarks.stream().forEach(a -> rtr.add(new CsvConcatenator(getClass(), a)));

		return rtr.toArray(new ITestSummary[rtr.size()]);
	}

	private static List<Class<? extends ICsvProviderProvider<? extends Object>>> getBenchmarks() {
		final List<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);
		benchmarks.add(GraphSizeCsvProvider.class);
		benchmarks.add(FastUPRBenchmark.class);
		return benchmarks;
	}

	/**
	 * Describe which columns should be present in the generated LaTeX table, based on the available
	 * {@link ICsvProviderProvider} instances during the test. Look in {@link InterpolationTestSuite} for an example.
	 */
	protected ColumnDefinition[] getColumnDefinitions() {
		return new ColumnDefinition[] { new ColumnDefinition("Runtime (ns)", "Avg. runtime",
				ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average), };
	}

}
