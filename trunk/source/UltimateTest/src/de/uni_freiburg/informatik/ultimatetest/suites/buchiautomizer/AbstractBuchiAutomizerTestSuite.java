package de.uni_freiburg.informatik.ultimatetest.suites.buchiautomizer;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TerminationAnalysisTestResultDecider;
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

public abstract class AbstractBuchiAutomizerTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition) {
		return new TerminationAnalysisTestResultDecider(ultimateRunDefinition, true);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = 
				new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);

		ColumnDefinition[] columnDef = new ColumnDefinition[] { new ColumnDefinition(
				"Runtime (ns)", "Avg. runtime",
				ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average) };

		return new ITestSummary[] { 
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), BuchiAutomizerTimingBenchmark.class), 
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
