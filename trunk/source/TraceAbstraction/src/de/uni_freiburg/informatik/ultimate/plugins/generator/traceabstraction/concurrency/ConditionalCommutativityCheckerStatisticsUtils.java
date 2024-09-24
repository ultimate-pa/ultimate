package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;

// TODO decouple statistics from CegarLoopStatisticsGenerator!
// The classes for conditional commutativity should collect their own statistics,
// which may in the end be added to the CEGAR loop's statistics.
public class ConditionalCommutativityCheckerStatisticsUtils implements IConditionalCommutativityCheckerStatisticsUtils {

	private final CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	public ConditionalCommutativityCheckerStatisticsUtils(final CegarLoopStatisticsGenerator cegarLoopBenchmark) {
		mCegarLoopBenchmark = cegarLoopBenchmark;
	}

	@Override
	public void startStopwatch() {
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.ConditionalCommutativityCheckTime);
	}

	@Override
	public void stopStopwatch() {
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.ConditionalCommutativityCheckTime);
	}

	@Override
	public void addDFSRestart() {
		mCegarLoopBenchmark.addConditionalCommutativityDFSRestart();
	}

	@Override
	public void addIAIntegration() {
		mCegarLoopBenchmark.addConditionalCommutativityIAIntegration();
	}

	@Override
	public void addConditionCalculation() {
		mCegarLoopBenchmark.addConditionalCommutativityConditionCalculation();
	}

	@Override
	public void addTraceCheck() {
		mCegarLoopBenchmark.addConditionalCommutativityTraceCheck();
	}

	@Override
	public void addImperfectProof() {
		mCegarLoopBenchmark.addConditionalCommutativityImperfectProof();
	}
}
