package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;

/**
 * A VariantGenerator can apply arbitrary subsets of a given set of (opaque) changes to the input source code to
 * generate different variants. It separates the computation of potential changes and the whole source code
 * transformation in general from the search for a reduced source variant and allows to use various search algorithms.
 *
 * An implementation can compute a new set of changes that depends on the outcome of a search. This allows for
 * alternative and hierarchical transformations that depend on the outcome of other transformations.
 */
public interface VariantGenerator {

	/**
	 * Applies the given subset of changes and returns the modified source code text.
	 *
	 * This method implementation must be thread safe to allow parallel generation of variants.
	 *
	 * A ChangeConflictException can be thrown to indicate that the particular subset of changes cannot be applied
	 * together, but (most) other variants could still be generated. Any other exception is an unexpected and possibly
	 * unrecoverable error and should be treated accordingly.
	 *
	 * @param activeChanges
	 *            <em>subsequence</em> of the list of getChanges() that contains the changes to apply
	 * @return rewritten source code text with the selected changes applied
	 * @throws ChangeConflictException
	 *             if not all changes could not be applied
	 */
	String apply(List<ChangeHandle> activeChanges);

	/**
	 * @return list of available changes, never empty
	 */
	List<ChangeHandle> getChanges();

	/**
	 * Optionally returns a new generator for another set of potential changes, that can be applied in addition to the
	 * given set of active changes.
	 *
	 * This method implementation is not required to be thread safe.
	 *
	 * @param activeChanges
	 *            subset of changes to keep and compute additional changes with
	 * @return a new generator instance if more changes exist
	 */
	default Optional<VariantGenerator> next(final List<ChangeHandle> activeChanges) {
		return Optional.empty();
	}
}
