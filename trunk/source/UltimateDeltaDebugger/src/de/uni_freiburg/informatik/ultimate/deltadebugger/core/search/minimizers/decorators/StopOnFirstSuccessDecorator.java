package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms.FinalMinimizerStep;

/**
 * Stop after the first successful reduction. Probably useless except for testing.
 */
public class StopOnFirstSuccessDecorator implements IMinimizer {
	private final IMinimizer mDelegateMinimizer;
	
	/**
	 * @param minimizer
	 *            Delegate minimizer.
	 */
	public StopOnFirstSuccessDecorator(final IMinimizer minimizer) {
		mDelegateMinimizer = minimizer;
	}
	
	@Override
	public <E> IMinimizerStep<E> create(final List<E> input) {
		return new StepDecorator<>(mDelegateMinimizer.create(input));
	}
	
	@Override
	public boolean isEachVariantUnique() {
		return mDelegateMinimizer.isEachVariantUnique();
	}
	
	@Override
	public boolean isResultMinimal() {
		return mDelegateMinimizer.isResultMinimal();
	}
	
	/**
	 * @param minimizer
	 *            Minimizer.
	 * @return the minimizer wrapped in a {@link StopOnFirstSuccessDecorator} if not already of this type
	 */
	public static IMinimizer decorate(final IMinimizer minimizer) {
		return minimizer instanceof StopOnFirstSuccessDecorator
				? minimizer
				: new StopOnFirstSuccessDecorator(minimizer);
	}
	
	/**
	 * A step decorator.
	 *
	 * @param <E>
	 *            element type
	 */
	static final class StepDecorator<E> implements IMinimizerStep<E> {
		private final IMinimizerStep<E> mDelegate;
		
		private StepDecorator(final IMinimizerStep<E> delegate) {
			mDelegate = delegate;
		}
		
		@Override
		public List<E> getResult() {
			return mDelegate.getResult();
		}
		
		@Override
		public List<E> getVariant() {
			return mDelegate.getVariant();
		}
		
		@Override
		public boolean isDone() {
			return mDelegate.isDone();
		}
		
		@Override
		public IMinimizerStep<E> next(final boolean keepVariant) {
			final IMinimizerStep<E> nextSstep = mDelegate.next(keepVariant);
			return keepVariant ? new FinalMinimizerStep<>(nextSstep.getResult()) : new StepDecorator<>(nextSstep);
		}
	}
}
