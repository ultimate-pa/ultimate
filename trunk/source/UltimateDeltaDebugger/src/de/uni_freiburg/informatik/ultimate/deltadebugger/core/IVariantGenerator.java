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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;

/**
 * A VariantGenerator can apply arbitrary subsets of a given set of (opaque) changes to the input source code to
 * generate different variants. It separates the computation of potential changes and the whole source code
 * transformation in general from the search for a reduced source variant and allows to use various search algorithms.
 * <p>
 * An implementation can compute a new set of changes that depends on the outcome of a search. This allows for
 * alternative and hierarchical transformations that depend on the outcome of other transformations.
 */
public interface IVariantGenerator {
	/**
	 * Applies the given subset of changes and returns the modified source code text.
	 * <p>
	 * This method implementation must be thread safe to allow parallel generation of variants.
	 * <p>
	 * A {@link ChangeConflictException} can be thrown to indicate that the particular subset of changes cannot be
	 * applied together, but (most) other variants could still be generated. Any other exception is an unexpected and
	 * possibly unrecoverable error and should be treated accordingly.
	 *
	 * @param activeChanges
	 *            <em>subsequence</em> of the list of getChanges() that contains the changes to apply
	 * @return rewritten source code text with the selected changes applied
	 */
	String apply(List<IChangeHandle> activeChanges);
	
	/**
	 * @return A list of available changes, never empty.
	 */
	List<IChangeHandle> getChanges();
	
	/**
	 * Optionally returns a new generator for another set of potential changes that can be applied in addition to the
	 * given set of active changes.
	 * <p>
	 * This method implementation is not required to be thread safe.
	 *
	 * @param activeChanges
	 *            subset of changes to keep and compute additional changes with
	 * @return a new generator instance if more changes exist
	 */
	default Optional<IVariantGenerator> next(final List<IChangeHandle> activeChanges) {
		return Optional.empty();
	}
}
