package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.reporting.CsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;

public abstract class AbstractTraceAbstractionTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, true);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = 
				new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(Benchmark.class);

		// @formatter:off
		ColumnDefinition[] columnDef = new ColumnDefinition[] { 
						new ColumnDefinition(
								"Overall time", "Avg. runtime",
								ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
//						new ColumnDefinition(
//								"Peak memory consumption (bytes)", "Mem{-}ory",
//								ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),						
						new ColumnDefinition(
								"Overall iterations", "Iter{-}ations",
								ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
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
//								ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),					
					};
				// @formatter:on

		return new ITestSummary[] { 
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class), 
				new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				new LatexDetailedSummary(getClass(), benchmarks, columnDef),
//				new CsvSummary(getClass(), benchmarks, columnDef),
				new HTMLSummary(getClass(), benchmarks, columnDef),
				new KingOfTheHillSummary(this.getClass()),
		};
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { 
			new IncrementalLogWithBenchmarkResults(this.getClass()),
			new IncrementalLogWithVMParameters(this.getClass(), getTimeout()),
		};
	}
}
