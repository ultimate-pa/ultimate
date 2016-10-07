package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.Minimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * Adds an empty variant as first step to another minimizer.
 */
public class IncludeEmptyVariantDecorator implements Minimizer {
	private final Minimizer delegate;

	public IncludeEmptyVariantDecorator(Minimizer delegate) {
		this.delegate = delegate;
	}
	
	public static Minimizer decorate(Minimizer minimizer) {
		return (minimizer instanceof IncludeEmptyVariantDecorator) ? minimizer
				: new IncludeEmptyVariantDecorator(minimizer);
	}

	@Override
	public <E> MinimizerStep<E> create(List<E> input) {
		if (input.isEmpty()) {
			return delegate.create(input);
		}
		return new StepDecorator<>(input);
	}

	@Override
	public boolean isResultMinimal() {
		return delegate.isResultMinimal();
	}

	@Override
	public boolean isEachVariantUnique() {
		return delegate.isEachVariantUnique();
	}


	final class StepDecorator<E> implements MinimizerStep<E> {
		final List<E> input;

		private StepDecorator(List<E> input) {
			this.input = input;
		}

		@Override
		public boolean isDone() {
			return false;
		}

		@Override
		public List<E> getVariant() {
			return Collections.emptyList();
		}

		@Override
		public MinimizerStep<E> next(boolean keepVariant) {
			return delegate.create(keepVariant ? Collections.emptyList() : input);
		}

		@Override
		public List<E> getResult() {
			return input;
		}
	}
}