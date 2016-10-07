package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * Adds an empty variant as first step to another minimizer.
 */
public class IncludeEmptyVariantDecorator implements Minimizer {
	final class StepDecorator<E> implements MinimizerStep<E> {
		final List<E> input;

		private StepDecorator(final List<E> input) {
			this.input = input;
		}

		@Override
		public List<E> getResult() {
			return input;
		}

		@Override
		public List<E> getVariant() {
			return Collections.emptyList();
		}

		@Override
		public boolean isDone() {
			return false;
		}

		@Override
		public MinimizerStep<E> next(final boolean keepVariant) {
			return delegate.create(keepVariant ? Collections.emptyList() : input);
		}
	}

	public static Minimizer decorate(final Minimizer minimizer) {
		return minimizer instanceof IncludeEmptyVariantDecorator ? minimizer
				: new IncludeEmptyVariantDecorator(minimizer);
	}

	private final Minimizer delegate;

	public IncludeEmptyVariantDecorator(final Minimizer delegate) {
		this.delegate = delegate;
	}

	@Override
	public <E> MinimizerStep<E> create(final List<E> input) {
		if (input.isEmpty()) {
			return delegate.create(input);
		}
		return new StepDecorator<>(input);
	}

	@Override
	public boolean isEachVariantUnique() {
		return delegate.isEachVariantUnique();
	}

	@Override
	public boolean isResultMinimal() {
		return delegate.isResultMinimal();
	}
}