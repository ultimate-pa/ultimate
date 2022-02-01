/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.List;
import java.util.Optional;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.IGeneratorSearchStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.ISpeculativeIterationObserver;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.ISpeculativeTask;

/**
 * Monitor for the search using a {@link IGeneratorSearchStep}.
 */
class SearchObserver implements ISpeculativeIterationObserver<IGeneratorSearchStep> {
	// k such that an info is printed in the debug logger for every k tests
	private static final int DEBUG_TEST_COUNT = 100;
	
	private final IVariantTestFunction mTestFunction;
	private final SearchStats mStats;
	private IGeneratorSearchStep mPreviousStep;
	
	private final ILogger mLogger;
	
	public SearchObserver(final IVariantTestFunction testFunction, final SearchStats stats, final ILogger logger) {
		mTestFunction = testFunction;
		mStats = stats;
		mLogger = logger;
	}
	
	/**
	 * Logs changes in the debug level.
	 * 
	 * @param changes
	 *            list of changes
	 */
	public void debugLogChangeDetails(final List<IChangeHandle> changes) {
		if (mLogger.isDebugEnabled()) {
			for (int i = 0; i != changes.size(); ++i) {
				mLogger.debug("[" + i + "] " + changes.get(i));
			}
		}
	}
	
	/**
	 * Logs search statistics in the info level.
	 * 
	 * @param logger
	 *            logger
	 * @param stats
	 *            search statistics
	 */
	public static void infoLogStats(final ILogger logger, final SearchStats stats) {
		if (logger.isInfoEnabled()) {
			logger.info("Overall test count: " + stats.getOverallTestCount());
			logger.info(" - successful: " + stats.getSuccessfulSteps());
			logger.info(
					" - failed: " + stats.getFailedSteps() + " (" + stats.getChangeConflicts() + " change conflicts)");
			logger.info(" - canceled: " + stats.getCanceledSpeculativeSteps());
			logger.info(" - duplicate tests skipped: " + stats.getSkippedDuplicateMinimizerSteps());
		}
	}
	
	@SuppressWarnings("squid:S1698")
	@Override
	public void onStepBegin(final IGeneratorSearchStep step) {
		// inequality intended here
		if (mPreviousStep == null || step.getVariantGenerator() != mPreviousStep.getVariantGenerator()) {
			// Handle change of variant generator
			if (mPreviousStep != null) {
				mLogger.debug("\n########################################################################");
				mLogger.debug(mPreviousStep.getActiveChanges().size() + " active changes found!");
				mLogger.debug("########################################################################\n");
				debugLogChangeDetails(mPreviousStep.getActiveChanges());
			}
			
			mLogger.debug("\n########################################################################");
			mLogger.debug("Searching over " + step.getVariantGenerator().getChanges().size() + " changes...");
			mLogger.debug("########################################################################\n");
			debugLogChangeDetails(step.getVariantGenerator().getChanges());
		}
		
		mPreviousStep = step;
	}
	
	@Override
	public void onStepComplete(final IGeneratorSearchStep step, final boolean keepVariant) {
		// Update the duplicate tracker with the result, now that we know
		// that this step is valid
		step.updateDuplicateTrackerWithTestResult(keepVariant);
		
		if (keepVariant) {
			mStats.incrementSuccessfulSteps();
			mLogger.info("Success: " + step.getVariant().length() + " bytes");
		} else {
			mStats.incrementFailedSteps();
		}
		
		if (0 == mStats.getOverallTestCount().get() % DEBUG_TEST_COUNT) {
			infoLogStats(mLogger, mStats);
		}
	}
	
	@Override
	public void onTasksCanceled(final List<? extends ISpeculativeTask<IGeneratorSearchStep>> tasks) {
		mStats.addToCanceledSpeculativeSteps(tasks.size());
	}
	
	/**
	 * This method is called by the step iterator, possibly from multiple threads in parallel. Forwards the call to the
	 * external test if the variant string can be generated.
	 *
	 * @param step
	 *            search step
	 * @param isCanceled
	 *            {@code true} if the run is canceled
	 * @return the result if not canceled
	 */
	Optional<Boolean> runTestForStep(final IGeneratorSearchStep step, final BooleanSupplier isCanceled) {
		mStats.getOverallTestCount().incrementAndGet();
		
		String variant;
		try {
			variant = step.getVariant();
		} catch (final ChangeConflictException e) {
			mLogger.warn("Skipping test because of change conflict: " + e.getMessage());
			mLogger.debug("change conflict details " + e);
			
			mStats.getChangeConflicts().incrementAndGet();
			return Optional.of(Boolean.FALSE);
		}
		
		if (isCanceled.getAsBoolean()) {
			return Optional.empty();
		}
		
		return mTestFunction.cancelableTest(variant, isCanceled);
	}
}
