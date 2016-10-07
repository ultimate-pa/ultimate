package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import org.apache.log4j.Logger;

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
	static Logger logger = Logger.getLogger(PassRunner.class);

	private List<PassDescription> passes = Collections.emptyList();
	private VariantTestFunction testFunction; // required
	private PassContextFactory contextFactory = DefaultPassContext::new;
	private Minimizer defaultMinimizer = IncludeEmptyVariantDecorator.decorate(new BinarySearchMinimizer(false));
	private ExecutorService executorService;
	private int workerCount = 1;
	private int timeLimitPerPassInSeconds = 0;

	private SearchStats stats = new SearchStats();

	public List<PassDescription> getPasses() {
		return passes;
	}

	public PassRunner setPasses(List<PassDescription> passes) {
		this.passes = Objects.requireNonNull(passes);
		return this;
	}

	public PassRunner setPasses(PassDescription... passes) {
		this.passes = Arrays.asList(passes);
		return this;
	}

	public VariantTestFunction getTestFunction() {
		return testFunction;
	}

	public PassRunner setTestFunction(VariantTestFunction testFunction) {
		this.testFunction = Objects.requireNonNull(testFunction);
		return this;
	}

	public PassContextFactory getContextFactory() {
		return contextFactory;
	}

	public PassRunner setContextFactory(PassContextFactory contextFactory) {
		this.contextFactory = Objects.requireNonNull(contextFactory);
		return this;
	}

	public Minimizer getDefaultMinimizer() {
		return defaultMinimizer;
	}

	public PassRunner setDefaultMinimizer(Minimizer defaultMinimizer) {
		this.defaultMinimizer = defaultMinimizer;
		return this;
	}

	public ExecutorService getExecutorService() {
		return executorService;
	}

	public int getWorkerCount() {
		return workerCount;
	}

	public PassRunner enableParallelTesting(ExecutorService executorService, int workerCount) {
		if (workerCount < 1) {
			throw new IllegalArgumentException();
		}

		this.executorService = Objects.requireNonNull(executorService);
		this.workerCount = workerCount;
		return this;
	}

	public PassRunner disableParallelTesting() {
		this.executorService = null;
		this.workerCount = 1;
		return this;
	}

	public boolean isParallelTestingEnabled() {
		return executorService != null;
	}

	public int getTimeLimitPerPassInSeconds() {
		return timeLimitPerPassInSeconds;
	}

	public void setTimeLimitPerPassInSeconds(int timeLimitPerPassInSeconds) {
		if (timeLimitPerPassInSeconds < 0) {
			throw new IllegalArgumentException();
		}
		this.timeLimitPerPassInSeconds = timeLimitPerPassInSeconds;
	}

	public SearchStats getStats() {
		return stats;
	}

	public void resetStats() {
		stats = new SearchStats();
	}

	/**
	 * @param input
	 *            input source code string
	 * @return
	 * @throws IllegalStateException
	 *             if no test function has been set
	 */
	public Optional<String> run(String input) {
		if (testFunction == null) {
			throw new IllegalStateException("missing test function");
		}

		Optional<String> result = Optional.empty();
		PassContext context = contextFactory.create(input);

		for (int i = 0; i != passes.size(); ++i) {
			final PassDescription pass = passes.get(i);

			logger.info("\n-------------------------");
			logger.info("Pass: " + pass.getName());
			logger.info("Description: " + pass.getDescription());
			logger.info("-------------------------\n");

			Optional<String> thisResult = applyPass(pass, context);
			if (thisResult.isPresent()) {
				// Create context using new best variant for the next pass, if
				// there is one
				if (i + 1 != passes.size() || pass.repeatUntilReductionFails()) {
					context = contextFactory.create(thisResult.get());
				}
				result = thisResult;
				
				if (pass.repeatUntilReductionFails()) {
					--i;
				}
			}
			logger.info("\n-------------------------\n");
			SearchObserver.debugLogStats(stats);
			logger.info("\n-------------------------\n");
		}
		
		return result;
	}

	

	Optional<String> applyPass(PassDescription pass, PassContext context) {
		Optional<VariantGenerator> generator = pass.getVariantGeneratorFactory().analyze(context);
		if (!generator.isPresent()) {
			return Optional.empty();
		}

		final Minimizer minmizer = pass.getMinimizer().orElse(defaultMinimizer);
		final boolean useSpeculativeIteration = executorService != null && !pass.disableSpeculativeTesting();

		return applyGenerators(generator.get(), minmizer, useSpeculativeIteration);
	}

	Optional<String> applyGenerators(VariantGenerator firstGenerator, Minimizer minimizer,
			boolean useSpeculativeIteration) {
		final SearchObserver observer = new SearchObserver(testFunction, stats);
		final GeneratorSearchStepFactory searchStepFactory = new GeneratorSearchStepFactory(minimizer,
				this::createDuplicateVariantTrackerLinkedToStats);
		final SpeculativeSearchIterator<GeneratorSearchStep> stepIterator = new SpeculativeSearchIterator<>(
				searchStepFactory.create(firstGenerator), observer);

		
		final int successfulStepsBefore = stats.successfulSteps;
		
		GeneratorSearchStep lastStep;
		if (useSpeculativeIteration) {
			lastStep = iterateParallel(new ParallelSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		} else {
			lastStep = iterateDirect(new DirectSearchIteratorIterator<>(stepIterator, observer::runTestForStep));
		}

		return successfulStepsBefore != stats.successfulSteps ? Optional.of(lastStep.getResult()) : Optional.empty();
	}

	GeneratorSearchStep iterateParallel(ParallelSearchIteratorIterator<GeneratorSearchStep> iterIterator) {
		iterIterator.beginIteration(executorService, workerCount);
		try {
			if (timeLimitPerPassInSeconds > 0
					&& !iterIterator.waitForEnd(timeLimitPerPassInSeconds, TimeUnit.SECONDS)) {
				logger.warn("Stopping search after " + timeLimitPerPassInSeconds + " seconds...");
				iterIterator.stopWorkers();
			}

			return iterIterator.endIteration();
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new UncheckedInterruptedException(e);
		}
	}

	GeneratorSearchStep iterateDirect(DirectSearchIteratorIterator<GeneratorSearchStep> iterIterator) {
		if (timeLimitPerPassInSeconds > 0) {
			if (!iterIterator.iterateFor(timeLimitPerPassInSeconds, TimeUnit.SECONDS)) {
				logger.warn("Stopping search after " + timeLimitPerPassInSeconds + " seconds...");
			}
		} else {
			iterIterator.iterateToEnd();
		}

		return iterIterator.getCurrentStep();
	}

	DuplicateVariantTracker<ChangeHandle> createDuplicateVariantTracker(Minimizer minimizer,
			List<ChangeHandle> allChanges) {
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

	DuplicateVariantTracker<ChangeHandle> createDuplicateVariantTrackerLinkedToStats(Minimizer minimizer,
			List<ChangeHandle> allChanges) {
		return new HitCountingDuplicateVariantTracker(createDuplicateVariantTracker(minimizer, allChanges),
				stats.skippedDuplicateMinimizerSteps);
	}
}