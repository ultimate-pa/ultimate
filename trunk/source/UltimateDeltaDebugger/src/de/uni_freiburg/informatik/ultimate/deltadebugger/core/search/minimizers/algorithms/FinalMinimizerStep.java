package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.List;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.MinimizerStep;

/**
 * Final minimizer state, only carries the result.
 *
 * @param <E> element type
 */
public class FinalMinimizerStep<E> implements MinimizerStep<E> {
	final List<E> result;

	/**
	 * The constructor.
	 * @param result
	 */
	public FinalMinimizerStep(List<E> result) {
		this.result = result;
	}

	@Override
	public boolean isDone() {
		return true;
	}

	@Override
	public List<E> getVariant() {
		throw new IllegalStateException();
	}

	@Override
	public MinimizerStep<E> next(boolean keepVariant) {
		throw new NoSuchElementException();
	}

	@Override
	public List<E> getResult() {
		return result;
	}
}