package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;

/**
 * Adds an empty variant as first step to another minimizer.
 */
public class IncludeEmptyVariantDecorator implements IMinimizer {
	private final IMinimizer mDelegate;
	
	/**
	 * @param delegate
	 *            Delegate minimizer.
	 */
	public IncludeEmptyVariantDecorator(final IMinimizer delegate) {
		mDelegate = delegate;
	}
	
	@Override
	public <E> IMinimizerStep<E> create(final List<E> input) {
		if (input.isEmpty()) {
			return mDelegate.create(input);
		}
		return new StepDecorator<>(input);
	}
	
	@Override
	public boolean isEachVariantUnique() {
		return mDelegate.isEachVariantUnique();
	}
	
	@Override
	public boolean isResultMinimal() {
		return mDelegate.isResultMinimal();
	}
	
	/**
	 * @param minimizer
	 *            Minimizer.
	 * @return the minimizer wrapped in an {@link IncludeEmptyVariantDecorator} if not already of this type
	 */
	public static IMinimizer decorate(final IMinimizer minimizer) {
		return minimizer instanceof IncludeEmptyVariantDecorator
				? minimizer
				: new IncludeEmptyVariantDecorator(minimizer);
	}
	
	/**
	 * A step decorator.
	 *
	 * @param <E>
	 *            element type
	 */
	final class StepDecorator<E> implements IMinimizerStep<E> {
		private final List<E> mInput;
		
		private StepDecorator(final List<E> input) {
			mInput = input;
		}
		
		@Override
		public List<E> getResult() {
			return mInput;
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
		public IMinimizerStep<E> next(final boolean keepVariant) {
			return mDelegate.create(keepVariant ? Collections.emptyList() : mInput);
		}
	}
}
