package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.HasSequenceIndex;

/**
 * Represents a change instance that can be independently enabled and disabled by a VariantGenerator.
 *
 */
public interface ChangeHandle extends HasSequenceIndex {
	/**
	 * Returns the index of this change in the sequence of all changes.
	 *
	 * This value can be used to to memoize the test result for a certain subset active of changes in a more memory
	 * efficient way than by storing the list itself. Besides that it can be used to assert that a certain subset of
	 * changes is actually a subsequence.
	 *
	 * @return index
	 */
	@Override
	int getSequenceIndex();

	/**
	 * @return Informative string representation for debugging purposes
	 */
	@Override
	String toString();
}
