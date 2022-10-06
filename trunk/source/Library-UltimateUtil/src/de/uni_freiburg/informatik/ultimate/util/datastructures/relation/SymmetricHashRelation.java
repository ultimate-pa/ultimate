/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2022 University of Freiburg
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

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Implementation of an HashRelation where the add method and the remove method make sure that that relation contains a
 * pair (a,b) iff the relation contains the pair (b,a).
 *
 * WARNING: If you use other ways to modify this relation (e.g., removal during iteration), the result might not be
 * symmetric any more.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <E>
 *            The type of elements in the relation.
 */
public class SymmetricHashRelation<E> extends HashRelation<E, E> {

	public SymmetricHashRelation() {
		super();
	}

	public SymmetricHashRelation(final AbstractRelation<E, E, ?, ?> rel) {
		super(rel);
	}

	@Override
	public boolean addPair(final E domainElem, final E rangeElem) {
		final boolean wasModified1 = super.addPair(domainElem, rangeElem);
		final boolean wasModified2 = super.addPair(rangeElem, domainElem);

		assert wasModified1 == wasModified2;

		return wasModified1;
	}

	@Override
	public boolean addAllPairs(final E domainElem, final Collection<E> rangeElems) {
		final boolean wasModified = super.addAllPairs(domainElem, rangeElems);
		for (final E rangeElem : rangeElems) {
			addPair(rangeElem, domainElem);
		}
		return wasModified;
	}

	@Override
	public boolean addAll(final AbstractRelation<E, E, ?, ?> rel) {
		final boolean wasModified = super.addAll(rel);

		if (!(rel instanceof SymmetricHashRelation<?>)) {
			for (final var entry : rel) {
				super.addPair(entry.getValue(), entry.getKey());
			}
		}

		return wasModified;
	}

	@Override
	public boolean reverseAddAll(final Map<E, E> map) {
		// This is fine as long as AbstractRelation internally calls #addPair
		return super.reverseAddAll(map);
	}

	@Override
	public boolean removePair(final E domainElem, final E rangeElem) {
		final boolean wasModified1 = super.removePair(domainElem, rangeElem);
		final boolean wasModified2 = super.removePair(rangeElem, domainElem);

		assert wasModified1 == wasModified2;

		return wasModified1;
	}

	@Override
	public void removeAllPairs(final AbstractRelation<E, E, ?, ?> rel) {
		// This is fine as long as AbstractRelation internally calls #removePair
		super.removeAllPairs(rel);
	}

	@Override
	public Set<E> removeDomainElement(final E elem) {
		final Set<E> rangeElems = super.removeDomainElement(elem);
		super.removeRangeElement(elem);
		return rangeElems;
	}

	@Override
	public void removeRangeElement(final E elem) {
		// On symmetric relations, removing a range element is the same as removing a domain element
		removeDomainElement(elem);
	}

	@Override
	public void replaceDomainElement(final E element, final E replacement) {
		super.replaceDomainElement(element, replacement);
		super.replaceRangeElement(element, replacement);
	}

	@Override
	public void replaceRangeElement(final E element, final E replacement) {
		// On symmetric relations, replacing a range element is the same as replacing a domain element
		replaceDomainElement(element, replacement);
	}

	public Set<Doubleton<E>> buildSetOfDoubletons() {
		final Set<Doubleton<E>> result = new HashSet<>();
		for (final Entry<E, E> entry : this) {
			result.add(new Doubleton<>(entry.getKey(), entry.getValue()));
		}
		return result;
	}

	// TODO Maybe this method should be renamed to buildSetOfNonReflexiveDoubletons ?
	public Set<Doubleton<E>> buildSetOfNonSymmetricDoubletons() {
		final Set<Doubleton<E>> result = new HashSet<>();
		for (final Entry<E, E> entry : this) {
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
