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
