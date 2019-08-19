/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifierStatisticsGenerator.PredicateUniferStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimizationStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogCsv;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public abstract class AbstractTraceAbstractionTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, true);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		final ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(Benchmark.class);

		// @formatter:off
		final ColumnDefinition[] columnDef = new ColumnDefinition[] {
						new ColumnDefinition(
								CegarLoopStatisticsDefinitions.OverallTime.toString(), "Avg. runtime",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
//						new ColumnDefinition(
//								"Peak memory consumption (bytes)", "Mem{-}ory",
//								ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
						new ColumnDefinition(
								CegarLoopStatisticsDefinitions.OverallIterations.toString(), "Iter{-}ations",
								ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(
								CegarLoopStatisticsDefinitions.TraceHistogramMax.toString(), "TrHist max",
								ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
//
//						new ColumnDefinition("InterpolantConsolidationBenchmark_InterpolantsDropped", "Interpolants dropped", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition("InterpolantConsolidationBenchmark_NewlyCreatedInterpolants", "Newly Created Interpolants", ConversionContext.Divide(1, 2, ""), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition("EdgeCheckerBenchmarkData_Sat", "Num Sats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition("EdgeCheckerBenchmarkData_Unsat", "Num Unsats", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition("EdgeCheckerBenchmarkData_Unknown", "Num Unknown", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),
//						new ColumnDefinition("EdgeCheckerBenchmarkData_NotChecked", "Num NotChecked", ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Sum),
//						new ColumnDefinition("InterpolantConsolidationBenchmark_NumOfHoareTripleChecks", "NumOfHTC{-}Checks{-}IC",
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Max),
//						new ColumnDefinition("InterpolantConsolidationBenchmark_TimeOfConsolidation", "Time{-}Of{-}Consol.",
//								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average)

//						new ColumnDefinition(
//								"NumberOfCodeBlocks", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"NumberOfCodeBlocksAsserted", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"SizeOfPredicatesFP", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"SizeOfPredicatesBP", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"Conjuncts in SSA", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"Conjuncts in UnsatCore", null,
//								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition(
//								"ICC %", "ICC",
//								ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average)
						new ColumnDefinition(CegarLoopStatisticsDefinitions.AutomataMinimizationStatistics.toString() + "_"
								+ AutomataMinimizationStatisticsDefinitions.AutomataMinimizationTime.toString(), "mnmz time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
//						new ColumnDefinition("BasicInterpolantAutomatonTime", "bia time",
//								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.HoareTripleCheckerStatistics.toString() + "_" + HoareTripleCheckerStatisticsDefinitions.Time.toString(), "htc time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.PredicateUnifierStatistics.toString() + "_" + PredicateUniferStatisticsDefinitions.Time.toString(), "pu time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.AutomataDifference.toString(), "adiff time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.traceCheckStatistics.toString() + "_" + TraceCheckStatisticsDefinitions.InterpolantComputationTime.toString(), "itp time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.traceCheckStatistics.toString() + "_" + TraceCheckStatisticsDefinitions.SatisfiabilityAnalysisTime.toString(), "check-sat time",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Ignore, Aggregate.Average),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.traceCheckStatistics.toString() + "_" + TraceCheckStatisticsDefinitions.InterpolantComputations.toString(), "itps",
								ConversionContext.Divide(1, 2, " s"), Aggregate.Ignore, Aggregate.Sum),
						new ColumnDefinition(CegarLoopStatisticsDefinitions.traceCheckStatistics.toString() + "_" + TraceCheckStatisticsDefinitions.PerfectInterpolantSequences.toString(), "perf. itps",
								ConversionContext.Divide(1, 2, " s"), Aggregate.Ignore, Aggregate.Sum),
					};
				// @formatter:on

		return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class),
				new CsvConcatenator(this.getClass(), CodeCheckBenchmarks.class),
				// new CsvConcatenator(this.getClass(), StatisticsData.class),
				new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				// new LatexDetailedSummary(getClass(), benchmarks, columnDef),
				new CsvSummary(getClass(), benchmarks, columnDef),
				// new HTMLSummary(getClass(), benchmarks, columnDef),
				new KingOfTheHillSummary(this.getClass()), new StandingsSummary(this.getClass()), };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()),
				new IncrementalLogWithVMParameters(this.getClass(), getTimeout()),
				new IncrementalLogCsv(this.getClass(), StatisticsData.class), };
	}
}
