package de.uni_freiburg.informatik.ultimatetest.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.LassoTerminationAnalysisBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.TimingBenchmark;
import de.uni_freiburg.informatik.ultimatetest.AbstractModelCheckerTestSuite;
import de.uni_freiburg.informatik.ultimatetest.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TerminationAnalysisTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.CsvConcatenator;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.traceabstraction.TestSummaryWithBenchmarkResults;

public abstract class AbstractBuchiAutomizerTestSuite extends AbstractModelCheckerTestSuite {

	@Override
	public ITestResultDecider constructITestResultDecider(
			UltimateRunDefinition ultimateRunDefinition) {
		return new TerminationAnalysisTestResultDecider(ultimateRunDefinition, true);
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] {
				new TestSummaryWithBenchmarkResults(this.getClass()),
				new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TimingBenchmark.class),
		};
	}

}
