package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

/**
 * A list element that knows it's own position in the minimizer's input sequence.
 */
@FunctionalInterface
public interface IHasSequenceIndex {
	/**
	 * @return The sequence index.
	 */
	int getSequenceIndex();
}
