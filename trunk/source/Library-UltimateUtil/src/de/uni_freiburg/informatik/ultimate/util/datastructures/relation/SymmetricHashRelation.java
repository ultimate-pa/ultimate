/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Implementation of the AbstractRelation that uses HashMap and HashSet.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public class SymmetricHashRelation<E> extends HashRelation<E, E> {

	public SymmetricHashRelation() {
		super();
	}

	public SymmetricHashRelation(final AbstractRelation<E, E, ?> rel) {
		super(rel);
	}

	@Override
	public boolean addPair(final E domainElem, final E rangeElem) {
		final boolean wasModified = super.addPair(domainElem, rangeElem);
		super.addPair(rangeElem, domainElem);
		return wasModified;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.util.datastructures.relation.
	 * AbstractRelation#removePair(java.lang.Object, java.lang.Object)
	 */
	@Override
	public boolean removePair(final E domainElem, final E rangeElem) {
		// Remove pair in both directions as it is considered to be symmetric
		final boolean containedPairFirstDirection = super.removePair(domainElem, rangeElem);
		final boolean containedPairSecondDirection = super.removePair(rangeElem, domainElem);

		// A valid symmetric relation always needs to hold both directions if any
		assert containedPairFirstDirection == containedPairSecondDirection;

		return containedPairFirstDirection;
	}

	public Set<Doubleton<E>> buildSetOfDoubletons() {
		final Set<Doubleton<E>> result = new HashSet<>();
		for (final Entry<E, E> entry : entrySet()) {
			result.add(new Doubleton<>(entry.getKey(), entry.getValue()));
		}
		return result;
	}

	public Set<Doubleton<E>> buildSetOfNonSymmetricDoubletons() {
		final Set<Doubleton<E>> result = new HashSet<>();
		for (final Entry<E, E> entry : entrySet()) {
			if (!entry.getKey().equals(entry.getValue())) {
				result.add(new Doubleton<>(entry.getKey(), entry.getValue()));
			}
		}
		return result;
	}

	/**
	 * Transform this relation into its transitive closure and return all the difference of the input and the transitive
	 * closure as set of doubletons.
	 */
	public Set<Doubleton<E>> makeTransitive() {
		final Set<Doubleton<E>> allAddedDoubletons = new HashSet<>();
		Set<Doubleton<E>> recentlyAddedDoubletons = this.buildSetOfDoubletons();
		while (!recentlyAddedDoubletons.isEmpty()) {
			final Set<Doubleton<E>> newDoubletons = new HashSet<>();
			for (final Doubleton<E> doubleton : recentlyAddedDoubletons) {
				for (final E third : getImage(doubleton.getOneElement())) {
					if (!containsPair(doubleton.getOtherElement(), third)) {
						newDoubletons.add(new Doubleton<>(doubleton.getOtherElement(), third));
					}
				}
				for (final E third : getImage(doubleton.getOtherElement())) {
					if (!containsPair(doubleton.getOneElement(), third)) {
						newDoubletons.add(new Doubleton<>(doubleton.getOneElement(), third));
					}
				}
			}
			recentlyAddedDoubletons = newDoubletons;
			for (final Doubleton<E> doubleton : newDoubletons) {
				this.addPair(doubleton.getOneElement(), doubleton.getOtherElement());
			}
			allAddedDoubletons.addAll(newDoubletons);
		}
		return allAddedDoubletons;
	}

}
