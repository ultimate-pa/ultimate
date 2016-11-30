package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

import java.util.List;

/**
 * Represents an iterative minimization algorithm.
 *
 * @see IMinimizerStep
 */
public interface IMinimizer {
	/**
	 * Create the initial algorithm state to minimize the given input sequence.
	 *
	 * @param input
	 *            input sequence
	 * @param <E>
	 *            element type
	 * @return initial algorithm state
	 */
	<E> IMinimizerStep<E> create(List<E> input);
	
	/**
	 * @return Whether duplicate variants may be generated or not.
	 */
	boolean isEachVariantUnique();
	
	/**
	 * Returns whether the result is a local minimum wrt. this minimizer. This flag tell whether applying the same
	 * minimizer again may result in a further reduction or not. It does not mean the result is a globally minimal and
	 * not even one-minimal.
	 *
	 * @return whether the result is locally minimal or not
	 */
	boolean isResultMinimal();
}
