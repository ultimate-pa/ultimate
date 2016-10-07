package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.FinalMinimizerStep;

/**
 * Stop after the first successful reduction. Probably useless except for
 * testing.
 */
public class StopOnFirstSuccessDecorator implements Minimizer {
	final Minimizer delegateMinimizer;

	public StopOnFirstSuccessDecorator(Minimizer minimizer) {
		this.delegateMinimizer = minimizer;
	}

	public static Minimizer decorate(Minimizer minimizer) {
		return (minimizer instanceof StopOnFirstSuccessDecorator) ? minimizer
				: new StopOnFirstSuccessDecorator(minimizer);
	}

	@Override
	public <E> MinimizerStep<E> create(List<E> input) {
		return new StepDecorator<>(delegateMinimizer.create(input));
	}

	@Override
	public boolean isResultMinimal() {
		return delegateMinimizer.isResultMinimal();
	}

	@Override
	public boolean isEachVariantUnique() {
		return delegateMinimizer.isEachVariantUnique();
	}

	static final class StepDecorator<E> implements MinimizerStep<E> {
		final MinimizerStep<E> delegate;

		private StepDecorator(MinimizerStep<E> delegate) {
			this.delegate = delegate;
		}

		@Override
		public boolean isDone() {
			return delegate.isDone();
		}

		@Override
		public List<E> getVariant() {
			return delegate.getVariant();
		}

		@Override
		public MinimizerStep<E> next(boolean keepVariant) {
			final MinimizerStep<E> nextSstep = delegate.next(keepVariant);
			return keepVariant ? new FinalMinimizerStep<>(nextSstep.getResult()) : new StepDecorator<>(nextSstep);
		}

		@Override
		public List<E> getResult() {
			return delegate.getResult();
		}
	}
}