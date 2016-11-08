package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.List;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;

/**
 * Final minimizer state, only carries the result.
 *
 * @param <E>
 *            element type
 */
public class FinalMinimizerStep<E> implements IMinimizerStep<E> {
	private final List<E> mResult;

	/**
	 * The constructor.
	 * 
	 * @param result
	 */
	public FinalMinimizerStep(final List<E> result) {
		this.mResult = result;
	}

	@Override
	public List<E> getResult() {
		return mResult;
	}

	@Override
	public List<E> getVariant() {
		throw new IllegalStateException();
	}

	@Override
	public boolean isDone() {
		return true;
	}

	@Override
	public IMinimizerStep<E> next(final boolean keepVariant) {
		throw new NoSuchElementException();
	}
}
