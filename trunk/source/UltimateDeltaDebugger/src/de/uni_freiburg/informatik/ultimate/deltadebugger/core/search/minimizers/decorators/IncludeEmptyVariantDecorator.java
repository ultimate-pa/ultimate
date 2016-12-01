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
