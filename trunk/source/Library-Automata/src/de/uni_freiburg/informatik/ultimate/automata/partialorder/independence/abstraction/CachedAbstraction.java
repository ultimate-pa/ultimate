/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * An abstraction function that caches the result computed by an underlying abstraction function. This can be used to
 * avoid redundant computations, but also to ensure that similar inputs to the abstraction function yield (reference-)
 * equal abstracted letters.
 *
 * This class makes use of {@link #restrict(Object, Object)} to possibly lower the abstraction level, in order to re-use
 * cached abstractions for different levels (as long as {@link #restrict(Object, Object)} returns the same
 * representative level).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <H>
 *            The type of abstraction levels
 * @param <L>
 *            The type of letters to abstract
 */
public class CachedAbstraction<H, L> implements IAbstraction<H, L> {

	private final IAbstraction<H, L> mUnderlying;
	private final NestedMap2<L, H, L> mCache = new NestedMap2<>();

	/**
	 * Creates a new cached abstraction function.
	 *
	 * @param underlying
	 *            The underlying abstraction function to cache
	 */
	public CachedAbstraction(final IAbstraction<H, L> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public ILattice<H> getHierarchy() {
		return mUnderlying.getHierarchy();
	}

	@Override
	public L abstractLetter(final L input, final H level) {
		// First, try direct cache lookup.
		// (Do not restrict immediately, for performance purposes.)
		if (mCache.containsKey(input, level)) {
			return mCache.get(input, level);
		}

		// Restrict to a lower level, for which the result is still the same as for the given level.
		final H restricted = restrict(input, level);
		assert getHierarchy().compare(restricted, level)
				.isLessOrEqual() : "restrict must return smaller or equal abstraction level";

		// Try cache lookup at restricted level.
		if (mCache.containsKey(input, restricted)) {
			final L result = mCache.get(input, restricted);
			// Duplicate value at current level (for faster future lookups).
			mCache.put(input, level, result);
			return result;
		}

		// Result has not been cached. Compute it, and store it at the restricted level.
		final L abstracted = mUnderlying.abstractLetter(input, restricted);
		mCache.put(input, restricted, abstracted);
		return abstracted;
	}

	@Override
	public H restrict(final L input, final H level) {
		return mUnderlying.restrict(input, level);
	}
}
