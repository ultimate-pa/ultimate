package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.List;
import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.GeneratorSearchStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeIterationObserver;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeTask;

class SearchObserver implements SpeculativeIterationObserver<GeneratorSearchStep> {
	private final VariantTestFunction mTestFunction;

	private final SearchStats mStats;

	private GeneratorSearchStep previousStep;

	private final ILogger mLogger;

	public SearchObserver(final VariantTestFunction testFunction, final SearchStats stats, final ILogger logger) {
		mTestFunction = testFunction;
		mStats = stats;
		mLogger = logger;
	}

	public void debugLogChangeDetails(final List<ChangeHandle> changes) {
		for (int i = 0; i != changes.size(); ++i) {
			mLogger.debug("[" + i + "] " + changes.get(i));
		}
	}

	public static void debugLogStats(final ILogger logger, final SearchStats stats) {
		logger.info("Overall test count: " + stats.getOverallTestCount());
		logger.info(" - successful: " + stats.getSuccessfulSteps());
		logger.info(" - failed: " + stats.getFailedSteps() + " (" + stats.getChangeConflicts() + " change conflicts)");
		logger.info(" - canceled: " + stats.getCanceledSpeculativeSteps());
		logger.info(" - duplicate tests skipped: " + stats.getSkippedDuplicateMinimizerSteps());
	}

	@Override
	public void onStepBegin(final GeneratorSearchStep step) {
		if (previousStep == null || step.getVariantGenerator() != previousStep.getVariantGenerator()) {
			// Handle change of variant generator
			if (previousStep != null) {
				mLogger.debug("\n########################################################################");
				mLogger.debug(previousStep.getActiveChanges().size() + " active changes found!");
				mLogger.debug("########################################################################\n");
				debugLogChangeDetails(previousStep.getActiveChanges());
			}

			mLogger.debug("\n########################################################################");
			mLogger.debug("Searching over " + step.getVariantGenerator().getChanges().size() + " changes...");
			mLogger.debug("########################################################################\n");
			debugLogChangeDetails(step.getVariantGenerator().getChanges());
		}

		previousStep = step;
	}

	@Override
	public void onStepComplete(final GeneratorSearchStep step, final boolean keepVariant) {
		// Update the duplicate tracker with the result, now that we know
		// that this step is valid
		step.updateDuplicateTrackerWithTestResult(keepVariant);

		if (keepVariant) {
			++mStats.successfulSteps;
			mLogger.info("Success: " + step.getVariant().length() + " bytes");
		} else {
			++mStats.failedSteps;
		}

		if (0 == mStats.overallTestCount.get() % 100) {
			debugLogStats(mLogger, mStats);
		}

	}

	@Override
	public void onTasksCanceled(final List<? extends SpeculativeTask<GeneratorSearchStep>> tasks) {
		mStats.canceledSpeculativeSteps += tasks.size();
	}

	/**
	 * This method is called by the step iterator, possibly from multiple threads in parallel. Forwards the call to the
	 * external test if the variant string can be generated.
	 *
	 * @param step
	 * @param isCanceled
	 * @return
	 */
	Optional<Boolean> runTestForStep(final GeneratorSearchStep step, final BooleanSupplier isCanceled) {
		mStats.overallTestCount.incrementAndGet();

		String variant;
		try {
			variant = step.getVariant();
		} catch (final ChangeConflictException e) {
			mLogger.warn("Skipping test because of change conflict: " + e.getMessage());
			mLogger.debug("change conflict details " + e);

			mStats.changeConflicts.incrementAndGet();
			return Optional.of(false);
		}

		if (isCanceled.getAsBoolean()) {
			return Optional.empty();
		}

		return mTestFunction.cancelableTest(variant, isCanceled);
	}

}