package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UncheckedInterruptedException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.GeneratorSearchStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.GeneratorSearchStepFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.BinarySearchMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators.HitCountingDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators.IncludeEmptyVariantDecorator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.BitSetDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.HashSetDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers.NullDuplicateTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.DirectSearchIteratorIterator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.ParallelSearchIteratorIterator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.speculation.SpeculativeSearchIterator;

public class PassRunner {

	private VariantTestFunction testFunction; // required
	private List<PassDescription> mPasses;
	private PassContextFactory mContextFactory;
	private Minimizer mDefaultMinimizer;
	private ExecutorService mExecutorService;
	private int mWorkerCount;
	private int mTimeLimitPerPassInSeconds;

	private SearchStats mStats;

	protected final ILogger mLogger;

	public PassRunner(final ILogger logger) {
		mLogger = logger;
		mPasses = Collections.emptyList();
		mContextFactory = DefaultPassContext::new;
		mWorkerCount = 1;
		mTimeLimitPerPassInSeconds = 0;
		mStats = new SearchStats();
		mDefaultMinimizer = IncludeEmptyVariantDecorator.decorate(new BinarySearchMinimizer(false));
	}

	Optional<String> applyGenerators(final VariantGenerator firstGenerator, final Minimizer minimizer,
			final boolean useSpeculativeIteration) {
		final SearchObserver observer = new SearchObserver(testFunction, mStats, mLogger);
		final GeneratorSearchStepFactory searchStepFactory =
				new GeneratorSearchStepFactory(minimizer, this::createDuplicateVariantTrackerLinkedToStats);
		final SpeculativeSearchIterator<GeneratorSearchStep> stepIterator =
				new SpeculativeSearchIterator<>(searchStepFactory.create(firstGenerator), observer);

		final int successfulStepsBefore = mStats.successfulSteps;

		GeneratorSearchStep lastStep;
		if (useSpeculativeIteration) {
			lastStep = iterateParallel(new ParallelSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		} else {
			lastStep = iterateDirect(new DirectSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		}

		return successfulStepsBefore != mStats.successfulSteps ? Optional.of(lastStep.getResult()) : Optional.empty();
	}

	Optional<String> applyPass(final PassDescription pass, final PassContext context) {
		final Optional<VariantGenerator> generator = pass.getVariantGeneratorFactory().analyze(context);
		if (!generator.isPresent()) {
			return Optional.empty();
		}

		final Minimizer minmizer = pass.getMinimizer().orElse(mDefaultMinimizer);
		final boolean useSpeculativeIteration = mExecutorService != null && !pass.disableSpeculativeTesting();

		return applyGenerators(generator.get(), minmizer, useSpeculativeIteration);
	}

	DuplicateVariantTracker<ChangeHandle> createDuplicateVariantTracker(final Minimizer minimizer,
			final List<ChangeHandle> allChanges) {
		if (minimizer.isEachVariantUnique()) {
			return NullDuplicateTracker.getInstance();
		}

		// Arbitrary limit right now, should be a value where memory usage of
		// storing O(n^2) variant lists may become relevant
		if (allChanges.size() > 1000) {
			return BitSetDuplicateTracker.create();
		}

		return new HashSetDuplicateTracker<>();
	}

	DuplicateVariantTracker<ChangeHandle> createDuplicateVariantTrackerLinkedToStats(final Minimizer minimizer,
			final List<ChangeHandle> allChanges) {
		return new HitCountingDuplicateVariantTracker(createDuplicateVariantTracker(minimizer, allChanges),
				mStats.skippedDuplicateMinimizerSteps);
	}

	public PassRunner disableParallelTesting() {
		mExecutorService = null;
		mWorkerCount = 1;
		return this;
	}

	public PassRunner enableParallelTesting(final ExecutorService executorService, final int workerCount) {
		if (workerCount < 1) {
			throw new IllegalArgumentException();
		}

		mExecutorService = Objects.requireNonNull(executorService);
		mWorkerCount = workerCount;
		return this;
	}

	public PassContextFactory getContextFactory() {
		return mContextFactory;
	}

	public Minimizer getDefaultMinimizer() {
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

	public VariantTestFunction getTestFunction() {
		return testFunction;
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

	GeneratorSearchStep iterateDirect(final DirectSearchIteratorIterator<GeneratorSearchStep> iterIterator) {
		if (mTimeLimitPerPassInSeconds > 0) {
			if (!iterIterator.iterateFor(mTimeLimitPerPassInSeconds, TimeUnit.SECONDS)) {
				mLogger.warn("Stopping search after " + mTimeLimitPerPassInSeconds + " seconds...");
			}
		} else {
			iterIterator.iterateToEnd();
		}

		return iterIterator.getCurrentStep();
	}

	GeneratorSearchStep iterateParallel(final ParallelSearchIteratorIterator<GeneratorSearchStep> iterIterator) {
		iterIterator.beginIteration(mExecutorService, mWorkerCount);
		try {
			if (mTimeLimitPerPassInSeconds > 0
					&& !iterIterator.waitForEnd(mTimeLimitPerPassInSeconds, TimeUnit.SECONDS)) {
				mLogger.warn("Stopping search after " + mTimeLimitPerPassInSeconds + " seconds...");
				iterIterator.stopWorkers();
			}

			return iterIterator.endIteration();
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new UncheckedInterruptedException(e);
		}
	}

	public void resetStats() {
		mStats = new SearchStats();
	}

	/**
	 * @param input
	 *            input source code string
	 * @return
	 * @throws IllegalStateException
	 *             if no test function has been set
	 */
	public Optional<String> run(final String input) {
		if (testFunction == null) {
			throw new IllegalStateException("missing test function");
		}

		Optional<String> result = Optional.empty();
		PassContext context = mContextFactory.create(input);

		for (int i = 0; i != mPasses.size(); ++i) {
			final PassDescription pass = mPasses.get(i);

			mLogger.info("\n-------------------------");
			mLogger.info("Pass: " + pass.getName());
			mLogger.info("Description: " + pass.getDescription());
			mLogger.info("-------------------------\n");

			final Optional<String> thisResult = applyPass(pass, context);
			if (thisResult.isPresent()) {
				// Create context using new best variant for the next pass, if
				// there is one
				if (i + 1 != mPasses.size() || pass.repeatUntilReductionFails()) {
					context = mContextFactory.create(thisResult.get());
				}
				result = thisResult;

				if (pass.repeatUntilReductionFails()) {
					--i;
				}
			}
			mLogger.info("\n-------------------------\n");
			SearchObserver.debugLogStats(mLogger, mStats);
			mLogger.info("\n-------------------------\n");
		}

		return result;
	}

	public PassRunner setContextFactory(final PassContextFactory contextFactory) {
		mContextFactory = Objects.requireNonNull(contextFactory);
		return this;
	}

	public PassRunner setDefaultMinimizer(final Minimizer defaultMinimizer) {
		mDefaultMinimizer = defaultMinimizer;
		return this;
	}

	public PassRunner setPasses(final List<PassDescription> passes) {
		mPasses = Objects.requireNonNull(passes);
		return this;
	}

	public PassRunner setPasses(final PassDescription... passes) {
		mPasses = Arrays.asList(passes);
		return this;
	}

	public PassRunner setTestFunction(final VariantTestFunction testFunction) {
		this.testFunction = Objects.requireNonNull(testFunction);
		return this;
	}

	public void setTimeLimitPerPassInSeconds(final int timeLimitPerPassInSeconds) {
		if (timeLimitPerPassInSeconds < 0) {
			throw new IllegalArgumentException();
		}
		mTimeLimitPerPassInSeconds = timeLimitPerPassInSeconds;
	}
}