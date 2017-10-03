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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.buchiautomizer;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimizationStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TerminationAnalysisTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

public abstract class AbstractBuchiAutomizerTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new TerminationAnalysisTestResultDecider(ultimateRunDefinition, true);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		final ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);

		final ColumnDefinition[] columnDef =
				new ColumnDefinition[] {
						new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "runtime",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						// new ColumnDefinition(
						// "Peak memory consumption (bytes)", "Mem{-}ory",
						// ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallIterations.toString(),
								"iter{-}ations", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore,
								Aggregate.Average),

						new ColumnDefinition(CegarLoopStatisticsDefinitions.AutomataDifference.toString(), "adiff time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),

						new ColumnDefinition("Dead end removal time", "dead end time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore,
								Aggregate.Average),
						new ColumnDefinition(
								CegarLoopStatisticsDefinitions.AutomataMinimizationStatistics.toString() + "_"
										+ AutomataMinimizationStatisticsDefinitions.AutomataMinimizationTime.toString(),
								"mnmz time", ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore,
								Aggregate.Average),
						new ColumnDefinition(
								CegarLoopStatisticsDefinitions.AutomataMinimizationStatistics.toString() + "_"
										+ AutomataMinimizationStatisticsDefinitions.StatesRemovedByMinimization
												.toString(),
								"mnmz states", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("BasicInterpolantAutomatonTime", "bia time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("EdgeCheckerBenchmarkData_EdgeCheckerTime", "ec time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("PredicateUnifierData_Time", "pu time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("traceCheckBenchmark_InterpolantComputationTime", "itp time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),

						new ColumnDefinition("NonLiveStateRemoval", "non live time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("BuchiClosure", "bc time", ConversionContext.Divide(1000000000, 2, " s"),
								Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition("LassoAnalysisTime", "lasso analysis time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),

						new ColumnDefinition("LassoNonterminationAnalysisTime", "gnta time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition("LassoNonterminationAnalysisSat", "gnta sat",
								ConversionContext.Divide(1, 0, ""), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition("LassoNonterminationAnalysisUnsat", "gnta unsat",
								ConversionContext.Divide(1, 0, ""), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition("LassoNonterminationAnalysisUnknown", "gnta unknown",
								ConversionContext.Divide(1, 0, ""), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition(BuchiCegarLoopBenchmark.s_MinimizationsOfDetermnisticAutomatomata,
								"mnmz det", ConversionContext.Divide(1, 0, ""), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition(BuchiCegarLoopBenchmark.s_MinimizationsOfNondetermnisticAutomatomata,
								"mnmz nondet", ConversionContext.Divide(1, 0, ""), Aggregate.Ignore, Aggregate.Sum), };

		return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), BuchiAutomizerTimingBenchmark.class),
				new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				new LatexDetailedSummary(getClass(), benchmarks, columnDef),
				// new CsvSummary(getClass(), benchmarks, columnDef),
				new HTMLSummary(getClass(), benchmarks, columnDef), new KingOfTheHillSummary(this.getClass()),
				new StandingsSummary(this.getClass()), };

	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()),
				new IncrementalLogWithVMParameters(this.getClass(), getTimeout()), };
	}

}
