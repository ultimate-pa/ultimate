package de.uni_freiburg.informatik.ultimatetest.suites;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.benchmark.SizeBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.suites.evals.TACAS2015;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.CsvSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.TraceAbstractionTestSummary;

public abstract class AbstractEvalTestSuite extends AbstractModelCheckerTestSuiteWithIncrementalLog {

	@Override
	protected ITestResultDecider constructITestResultDecider(UltimateRunDefinition ultimateRunDefinition) {
		return new SafetyCheckTestResultDecider(ultimateRunDefinition, false);
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { getIncrementalLogWithVMParameters(),
				new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);
		benchmarks.add(SizeBenchmark.class);

		ColumnDefinition[] columnDef = getColumnDefinitions();

		return new ITestSummary[] { new LatexOverviewSummary(getClass(), benchmarks, columnDef),
				new LatexDetailedSummary(getClass(), benchmarks, columnDef),
				new TraceAbstractionTestSummary(getClass()), new CsvSummary(getClass(), benchmarks, columnDef),
				new HTMLSummary(getClass(), benchmarks, columnDef), new KingOfTheHillSummary(this.getClass()), };
	}

	/**
	 * Describe which columns should be present in the generated LaTeX table,
	 * based on the available {@link ICsvProviderProvider} instances during the
	 * test. Look in {@link TACAS2015} for an example.
	 */
	protected abstract ColumnDefinition[] getColumnDefinitions();

}
