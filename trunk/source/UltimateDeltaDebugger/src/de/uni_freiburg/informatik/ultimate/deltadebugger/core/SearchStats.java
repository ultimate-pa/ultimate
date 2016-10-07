package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.concurrent.atomic.AtomicInteger;

public class SearchStats {
	int failedSteps;
	int successfulSteps;
	int canceledSpeculativeSteps;
	AtomicInteger skippedDuplicateMinimizerSteps = new AtomicInteger();
	AtomicInteger overallTestCount = new AtomicInteger();
	AtomicInteger changeConflicts = new AtomicInteger();

	public int getCanceledSpeculativeSteps() {
		return canceledSpeculativeSteps;
	}

	public int getChangeConflicts() {
		return changeConflicts.get();
	}

	public int getFailedSteps() {
		return failedSteps;
	}

	public int getOverallTestCount() {
		return overallTestCount.get();
	}

	public int getSkippedDuplicateMinimizerSteps() {
		return skippedDuplicateMinimizerSteps.get();
	}

	public int getSuccessfulSteps() {
		return successfulSteps;
	}
}