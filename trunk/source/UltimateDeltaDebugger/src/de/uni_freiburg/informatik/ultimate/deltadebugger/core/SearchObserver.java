package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.List;
import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.GeneratorSearchStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeIterationObserver;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeTask;

class SearchObserver implements SpeculativeIterationObserver<GeneratorSearchStep> {
	public static void debugLogChangeDetails(final List<ChangeHandle> changes) {
		for (int i = 0; i != changes.size(); ++i) {
			PassRunner.logger.debug("[" + i + "] " + changes.get(i));
		}
	}

	public static void debugLogStats(final SearchStats stats) {
		PassRunner.logger.info("Overall test count: " + stats.getOverallTestCount());
		PassRunner.logger.info(" - successful: " + stats.getSuccessfulSteps());
		PassRunner.logger.info(
				" - failed: " + stats.getFailedSteps() + " (" + stats.getChangeConflicts() + " change conflicts)");
		PassRunner.logger.info(" - canceled: " + stats.getCanceledSpeculativeSteps());
		PassRunner.logger.info(" - duplicate tests skipped: " + stats.getSkippedDuplicateMinimizerSteps());
	}

	private final VariantTestFunction testFunction;

	private final SearchStats stats;

	private GeneratorSearchStep previousStep;

	public SearchObserver(final VariantTestFunction testFunction, final SearchStats stats) {
		this.testFunction = testFunction;
		this.stats = stats;
	}

	@Override
	public void onStepBegin(final GeneratorSearchStep step) {
		if (previousStep == null || step.getVariantGenerator() != previousStep.getVariantGenerator()) {
			// Handle change of variant generator
			if (previousStep != null) {
				PassRunner.logger.debug("\n########################################################################");
				PassRunner.logger.debug(previousStep.getActiveChanges().size() + " active changes found!");
				PassRunner.logger.debug("########################################################################\n");
				debugLogChangeDetails(previousStep.getActiveChanges());
			}

			PassRunner.logger.debug("\n########################################################################");
			PassRunner.logger.debug("Searching over " + step.getVariantGenerator().getChanges().size() + " changes...");
			PassRunner.logger.debug("########################################################################\n");
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
			++stats.successfulSteps;
			PassRunner.logger.info("Success: " + step.getVariant().length() + " bytes");
		} else {
			++stats.failedSteps;
		}

		if (0 == stats.overallTestCount.get() % 100) {
			debugLogStats(stats);
		}

	}

	@Override
	public void onTasksCanceled(final List<? extends SpeculativeTask<GeneratorSearchStep>> tasks) {
		stats.canceledSpeculativeSteps += tasks.size();
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
		stats.overallTestCount.incrementAndGet();

		String variant;
		try {
			variant = step.getVariant();
		} catch (final ChangeConflictException e) {
			PassRunner.logger.warn("Skipping test because of change conflict: " + e.getMessage());
			PassRunner.logger.trace("change conflict details", e);

			stats.changeConflicts.incrementAndGet();
			return Optional.of(false);
		}

		if (isCanceled.getAsBoolean()) {
			return Optional.empty();
		}

		return testFunction.cancelableTest(variant, isCanceled);
	}

}