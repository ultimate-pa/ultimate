/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An independence relation that caches the result of an underlying relation. To
 * be used with computation-intensive independence relations.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class CachedIndependenceRelation<STATE, LETTER> implements IIndependenceRelation<STATE, LETTER> {

	private final IIndependenceRelation<STATE, LETTER> mUnderlying;
	private final Map<STATE, HashRelation<LETTER, LETTER>> mPositiveCache = new HashMap<>();
	private final Map<STATE, HashRelation<LETTER, LETTER>> mNegativeCache = new HashMap<>();

	public CachedIndependenceRelation(final IIndependenceRelation<STATE, LETTER> underlying) {
		mUnderlying = underlying;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public boolean contains(final STATE state, final LETTER a, final LETTER b) {
		STATE stateKey = state;
		if (!isConditional()) {
			stateKey = null;
		}

		HashRelation<LETTER, LETTER> positive = mPositiveCache.get(stateKey);
		if (positive == null) {
			positive = new HashRelation<>();
		}

		HashRelation<LETTER, LETTER> negative = mNegativeCache.get(stateKey);
		if (negative == null) {
			negative = new HashRelation<>();
		}

		if (positive.containsPair(a, b) || (isSymmetric() && positive.containsPair(b, a))) {
			return true;
		} else if (negative.containsPair(a, b) || (isSymmetric() && negative.containsPair(b, a))) {
			return false;
		}

		final boolean result = mUnderlying.contains(state, a, b);
		if (result) {
			positive.addPair(a, b);
			mPositiveCache.put(stateKey, positive);
		} else {
			negative.addPair(a, b);
			mNegativeCache.put(stateKey, negative);
		}

		return result;
	}

	public int getNegativeCacheSize() {
		final int negativeSize = mNegativeCache.entrySet().stream()
				.collect(Collectors.summingInt(e -> e.getValue().size()));
		return negativeSize;
	}

	public int getPositiveCacheSize() {
		final int positiveSize = mPositiveCache.entrySet().stream()
				.collect(Collectors.summingInt(e -> e.getValue().size()));
		return positiveSize;
	}

	/**
	 * Merges cached independencies for two letters into a combined letter. If both
	 * are independent from some third letter c, the combined letter will be
	 * independent from c as well.
	 *
	 * This method can be used to transfer knowledge about letters to a (sequential
	 * or choice) composition of these letters. The caller must ensure soundness, it
	 * is not checked against the underlying relation (as this would defeat the
	 * purpose).
	 *
	 * @param a
	 *            The first letter
	 * @param b
	 *            The second letter
	 * @param ab
	 *            The combination (e.g. sequential composition) of the previous two
	 *            letters.
	 */
	public void mergeIndependencies(LETTER a, LETTER b, LETTER ab) {
		for (final STATE state : mPositiveCache.keySet()) {
			final HashRelation<LETTER, LETTER> relation = mPositiveCache.get(state);
			// (a, c) + (b, c) -> (ab, c)
			for (final LETTER c : relation.getImage(a)) {
				if (relation.containsPair(b, c)) {
					relation.addPair(ab, c);
				}
			}
			// (c, a) + (c, b) -> (c, ab)
			for (final LETTER c : relation.getDomain()) {
				if (relation.containsPair(c, a) && relation.containsPair(c, b)) {
					relation.addPair(c, ab);
				}
			}
		}
	}

	public void removeFromCache(LETTER a) {
		for (final STATE state : mPositiveCache.keySet()) {
			final HashRelation<LETTER, LETTER> relation = mPositiveCache.get(state);
			relation.removeDomainElement(a);
			relation.removeRangeElement(a);
		}
		for (final STATE state : mNegativeCache.keySet()) {
			final HashRelation<LETTER, LETTER> relation = mNegativeCache.get(state);
			relation.removeDomainElement(a);
			relation.removeRangeElement(a);
		}
	}
}
