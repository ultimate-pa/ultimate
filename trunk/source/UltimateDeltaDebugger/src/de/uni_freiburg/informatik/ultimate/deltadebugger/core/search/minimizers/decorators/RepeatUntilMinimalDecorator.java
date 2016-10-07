package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * Ensure local minimality by restarting on the result until the size stays the
 * same.
 *
 */
public class RepeatUntilMinimalDecorator implements Minimizer {
	final Minimizer delegateMinimizer;

	public RepeatUntilMinimalDecorator(Minimizer delegate) {
		this.delegateMinimizer = delegate;
	}

	public static Minimizer decorate(Minimizer minimizer) {
		return minimizer.isResultMinimal() ? minimizer : new RepeatUntilMinimalDecorator(minimizer);
	}

	@Override
	public <E> MinimizerStep<E> create(List<E> input) {
		return new StepDecorator<>(delegateMinimizer.create(input), input.size());
	}

	@Override
	public boolean isResultMinimal() {
		return true;
	}

	@Override
	public boolean isEachVariantUnique() {
		return false;
	}

	final class StepDecorator<E> implements MinimizerStep<E> {
		final MinimizerStep<E> delegate;
		final int initialSize;

		private StepDecorator(MinimizerStep<E> delegate, int initialSize) {
			this.delegate = delegate;
			this.initialSize = initialSize;
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
			final MinimizerStep<E> nextStep = delegate.next(keepVariant);
			if (nextStep.isDone()) {
				// Restart if something was removed
				final List<E> result = nextStep.getResult();
				if (result.size() != initialSize) {
					return create(result);
				}
			}

			return new StepDecorator<>(nextStep, initialSize);
		}

		@Override
		public List<E> getResult() {
			return delegate.getResult();
		}
	}
}