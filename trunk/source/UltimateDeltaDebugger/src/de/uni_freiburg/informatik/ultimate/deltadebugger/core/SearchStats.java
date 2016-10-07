package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.concurrent.atomic.AtomicInteger;

public class SearchStats {
	int failedSteps;
	int successfulSteps;
	int canceledSpeculativeSteps;
	AtomicInteger skippedDuplicateMinimizerSteps = new AtomicInteger();
	AtomicInteger overallTestCount = new AtomicInteger();
	AtomicInteger changeConflicts = new AtomicInteger();

	public int getFailedSteps() {
		return failedSteps;
	}

	public int getSuccessfulSteps() {
		return successfulSteps;
	}

	public int getCanceledSpeculativeSteps() {
		return canceledSpeculativeSteps;
	}

	public int getSkippedDuplicateMinimizerSteps() {
		return skippedDuplicateMinimizerSteps.get();
	}

	public int getOverallTestCount() {
		return overallTestCount.get();
	}

	public int getChangeConflicts() {
		return changeConflicts.get();
	}
}