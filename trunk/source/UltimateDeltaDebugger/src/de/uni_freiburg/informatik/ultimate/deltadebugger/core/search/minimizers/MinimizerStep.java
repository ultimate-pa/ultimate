package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.SearchStep;

/**
 * Represents an individual step in an iterative minimization algorithm. Each
 * non-final state has a variant, which is a subsequence of the best
 * minimization result so far (which is initially the input).
 * 
 * <ul>
 * <li>Immutable and multithread safe
 * <li>Returned lists are subsequences of the initial input list, i.e. original
 * element order is preserved
 * <li>
 * </ul>
 * 
 * @see SearchStep
 * @param <E>
 *            element type
 */
public interface MinimizerStep<E> extends SearchStep<List<E>, MinimizerStep<E>> {

}
