package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.NoSuchElementException;

/**
 * Represents an individual step in an iterative search algorithm. Allows to iterate over algorithm states. Each
 * non-final state has a variant of certain type. The next state is computed depending on whether the current variant is
 * better than the current result or not.
 * The most important property is that each step is immutable so a lookahead at following states is easily possible
 * without affecting the current state. This also ensures thread safety.
 *
 * @param <T>
 *            variant type
 * @param <S>
 *            self type
 */
public interface ISearchStep<T, S extends ISearchStep<T, S>> {
	/**
	 * @return The best result so far, which is initially the input.
	 */
	T getResult();
	
	/**
	 * Returns the current variant. Only valid if isDone() returns true.
	 * <p>
	 * Throws an {@link IllegalStateException} if the iteration has completed.
	 *
	 * @return variant
	 */
	T getVariant();
	
	/**
	 * Returns true for the final state, i.e. when the iteration has completed and no more variants are left.
	 *
	 * @return true iff iteration is complete
	 */
	boolean isDone();
	
	/**
	 * Computes the next state depending on whether the current variant is better than the current result or not.
	 * <p>
	 * Throws a {@link NoSuchElementException} if this state is already final.
	 * 
	 * @param keepVariant
	 *            if true the current variant is a valid result
	 * @return next state
	 */
	S next(boolean keepVariant);
}
