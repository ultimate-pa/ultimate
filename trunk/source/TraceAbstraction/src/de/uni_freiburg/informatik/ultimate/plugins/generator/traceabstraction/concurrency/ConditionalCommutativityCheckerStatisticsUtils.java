package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;

public class ConditionalCommutativityCheckerStatisticsUtils implements IConditionalCommutativityCheckerStatisticsUtils {

	private CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	public ConditionalCommutativityCheckerStatisticsUtils(CegarLoopStatisticsGenerator cegarLoopBenchmark) {
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

}
