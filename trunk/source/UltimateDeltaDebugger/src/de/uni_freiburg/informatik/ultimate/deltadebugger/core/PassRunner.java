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

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UncheckedInterruptedException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.GeneratorSearchStepFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.IGeneratorSearchStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.BinarySearchMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators.HitCountingDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators.IncludeEmptyVariantDecorator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.BitSetDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.HashSetDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.NullDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.DirectSearchIteratorIterator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.ParallelSearchIteratorIterator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeSearchIterator;

/**
 * Runs passes.
 */
public class PassRunner {
	// This should be a value where memory usage of storing O(n^2) variant lists may become relevant.
	private static final int VARIANT_LIST_SIZE_FOR_HASH_SETS = 1000;
	
	protected final ILogger mLogger;
	
	// required
	private IVariantTestFunction mTestFunction;
	
	private List<PassDescription> mPasses;
	private IPassContextFactory mContextFactory;
	private IMinimizer mDefaultMinimizer;
	private ExecutorService mExecutorService;
	private int mWorkerCount;
	private int mTimeLimitPerPassInSeconds;
	
	private SearchStats mStats;
	
	/**
	 * @param logger
	 *            Logger.
	 */
	public PassRunner(final ILogger logger) {
		mLogger = logger;
		mPasses = Collections.emptyList();
		mContextFactory = source -> new DefaultPassContext(source, logger);
		mWorkerCount = 1;
		mTimeLimitPerPassInSeconds = 0;
		mStats = new SearchStats();
		mDefaultMinimizer = IncludeEmptyVariantDecorator.decorate(new BinarySearchMinimizer(false));
	}
	
	Optional<String> applyGenerators(final IVariantGenerator firstGenerator, final IMinimizer minimizer,
			final boolean useSpeculativeIteration) {
		final SearchObserver observer = new SearchObserver(mTestFunction, mStats, mLogger);
		final GeneratorSearchStepFactory searchStepFactory =
				new GeneratorSearchStepFactory(minimizer, this::createDuplicateVariantTrackerLinkedToStats);
		final SpeculativeSearchIterator<IGeneratorSearchStep> stepIterator =
				new SpeculativeSearchIterator<>(searchStepFactory.create(firstGenerator), observer);
		
		final int successfulStepsBefore = mStats.getSuccessfulSteps();
		
		IGeneratorSearchStep lastStep;
		if (useSpeculativeIteration) {
			lastStep = iterateParallel(new ParallelSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		} else {
			lastStep = iterateDirect(new DirectSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		}
		
		return successfulStepsBefore != mStats.getSuccessfulSteps()
				? Optional.of(lastStep.getResult())
				: Optional.empty();
	}
	
	Optional<String> applyPass(final PassDescription pass, final IPassContext context) {
		final Optional<IVariantGenerator> generator = pass.getVariantGeneratorFactory().analyze(context);
		if (!generator.isPresent()) {
			return Optional.empty();
		}
		
		final IMinimizer minmizer = pass.getMinimizer().orElse(mDefaultMinimizer);
		final boolean useSpeculativeIteration = mExecutorService != null && !pass.disableSpeculativeTesting();
		
		return applyGenerators(generator.get(), minmizer, useSpeculativeIteration);
	}
	
	static IDuplicateVariantTracker<IChangeHandle> createDuplicateVariantTracker(final IMinimizer minimizer,
			final List<IChangeHandle> allChanges) {
		if (minimizer.isEachVariantUnique()) {
			return NullDuplicateTracker.getInstance();
		}
		
		if (allChanges.size() > VARIANT_LIST_SIZE_FOR_HASH_SETS) {
			return BitSetDuplicateTracker.create();
		}
		
		return new HashSetDuplicateTracker<>();
	}
	
	IDuplicateVariantTracker<IChangeHandle> createDuplicateVariantTrackerLinkedToStats(final IMinimizer minimizer,
			final List<IChangeHandle> allChanges) {
		return new HitCountingDuplicateVariantTracker(createDuplicateVariantTracker(minimizer, allChanges),
				mStats.getSkippedDuplicateMinimizerSteps());
	}
	
	/**
	 * @return The pass runner where parallel testing was disabled.
	 */
	public PassRunner disableParallelTesting() {
		mExecutorService = null;
		mWorkerCount = 1;
		return this;
	}
	
	/**
	 * @param executorService
	 *            Executor service.
	 * @param workerCount
	 *            number of workers
	 * @return The pass runner where parallel testing was enabled.
	 */
	public PassRunner enableParallelTesting(final ExecutorService executorService, final int workerCount) {
		if (workerCount < 1) {
			throw new IllegalArgumentException();
		}
		
		mExecutorService = Objects.requireNonNull(executorService);
		mWorkerCount = workerCount;
		return this;
	}
	
	public IPassContextFactory getContextFactory() {
		return mContextFactory;
	}
	
	public IMinimizer getDefaultMinimizer() {
		return mDefaultMinimizer;
	}
	
	public ExecutorService getExecutorService() {
		return mExecutorService;
	}
	
	public List<PassDescription> getPasses() {
		return mPasses;
	}
	
	public SearchStats getStats() {
		return mStats;
	}
	
	public IVariantTestFunction getTestFunction() {
		return mTestFunction;
	}
	
	public int getTimeLimitPerPassInSeconds() {
		return mTimeLimitPerPassInSeconds;
	}
	
	public int getWorkerCount() {
		return mWorkerCount;
	}
	
	public boolean isParallelTestingEnabled() {
		return mExecutorService != null;
	}
	
	IGeneratorSearchStep iterateDirect(final DirectSearchIteratorIterator<IGeneratorSearchStep> iterIterator) {
		if (mTimeLimitPerPassInSeconds > 0) {
			if (!iterIterator.iterateFor(mTimeLimitPerPassInSeconds, TimeUnit.SECONDS) && mLogger.isWarnEnabled()) {
				mLogger.warn("Stopping search after " + mTimeLimitPerPassInSeconds + " seconds...");
			}
		} else {
			iterIterator.iterateToEnd();
		}
		
		return iterIterator.getCurrentStep();
	}
	
	IGeneratorSearchStep iterateParallel(final ParallelSearchIteratorIterator<IGeneratorSearchStep> iterIterator) {
		iterIterator.beginIteration(mExecutorService, mWorkerCount);
		try {
			if (mTimeLimitPerPassInSeconds > 0
					&& !iterIterator.waitForEnd(mTimeLimitPerPassInSeconds, TimeUnit.SECONDS)) {
				if (mLogger.isWarnEnabled()) {
					mLogger.warn("Stopping search after " + mTimeLimitPerPassInSeconds + " seconds...");
				}
				iterIterator.stopWorkers();
			}
			
			return iterIterator.endIteration();
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new UncheckedInterruptedException(e);
		}
	}
	
	/**
	 * Resets the search statistics.
	 */
	public void resetStats() {
		mStats = new SearchStats();
	}
	
	/**
	 * @param input
	 *            Input source code string.
	 * @return result of applying the passes
	 */
	public Optional<String> run(final String input) {
		if (mTestFunction == null) {
			throw new IllegalStateException("missing test function");
		}
		
		Optional<String> result = Optional.empty();
		IPassContext context = mContextFactory.create(input);
		
		int passIndex = 0;
		while (passIndex != mPasses.size()) {
			final PassDescription pass = mPasses.get(passIndex);
			
			if (mLogger.isInfoEnabled()) {
				mLogger.info("\n-------------------------");
				mLogger.info("Pass: " + pass.getName());
				mLogger.info("Description: " + pass.getDescription());
				mLogger.info("-------------------------\n");
			}
			
			final Optional<String> thisResult = applyPass(pass, context);
			if (thisResult.isPresent()) {
				// Create context using new best variant for the next pass if there is one
				if (passIndex + 1 != mPasses.size() || pass.repeatUntilReductionFails()) {
					context = mContextFactory.create(thisResult.get());
				}
				result = thisResult;
				
				if (pass.repeatUntilReductionFails()) {
					// TODO: Actually check if the result is a new variant by comparing the source text.
					//       VariantGenerators should not support changes that don't actually change anything, 
					//       but if they do anyways, this loop won't terminate.
					--passIndex;
				}
			}
			++passIndex;
			
			if (mLogger.isInfoEnabled()) {
				mLogger.info("\n-------------------------\n");
				SearchObserver.infoLogStats(mLogger, mStats);
				mLogger.info("\n-------------------------\n");
			}
		}
		
		return result;
	}
	
	public PassRunner setContextFactory(final IPassContextFactory contextFactory) {
		mContextFactory = Objects.requireNonNull(contextFactory);
		return this;
	}
	
	public PassRunner setDefaultMinimizer(final IMinimizer defaultMinimizer) {
		mDefaultMinimizer = defaultMinimizer;
		return this;
	}
	
	public PassRunner setPasses(final List<PassDescription> passes) {
		mPasses = Objects.requireNonNull(passes);
		return this;
	}
	
	public PassRunner setTestFunction(final IVariantTestFunction testFunction) {
		mTestFunction = Objects.requireNonNull(testFunction);
		return this;
	}
	
	/**
	 * @param timeLimitPerPassInSeconds
	 *            Time limit per pass in seconds.
	 */
	public void setTimeLimitPerPassInSeconds(final int timeLimitPerPassInSeconds) {
		if (timeLimitPerPassInSeconds < 0) {
			throw new IllegalArgumentException();
		}
		mTimeLimitPerPassInSeconds = timeLimitPerPassInSeconds;
	}
}
