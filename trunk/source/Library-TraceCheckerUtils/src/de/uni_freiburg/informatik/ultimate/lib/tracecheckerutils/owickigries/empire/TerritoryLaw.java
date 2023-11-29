/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.KingdomLaw;

/**
 * Class represents a pair of Territory and the corresponding Law.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class TerritoryLaw<PLACE, LETTER> {
	private final Territory<PLACE, LETTER> mTerritory;
	private IPredicate mLaw;
	private final BasicPredicateFactory mFactory;
	private final Function<PLACE, IPredicate> mPlaceToAssertion;

	/**
	 * Construct a Territory, Law pair using rooks law corresponding to the territory.
	 *
	 * @param territory
	 *            A Territory object.
	 * @param rookLaw
	 *            Law of a rook corresponding to territoy.
	 * @param placeToAssertion
	 *            Function which resolves an assertion PLACE to IPredicate.
	 * @param factory
	 *            Factory for Predicate operations
	 */
	public TerritoryLaw(final Territory<PLACE, LETTER> territory, final KingdomLaw<PLACE, LETTER> rookLaw,
			final Function<PLACE, IPredicate> placeToAssertion, final BasicPredicateFactory factory) {
		mTerritory = territory;
		mFactory = factory;
		mPlaceToAssertion = placeToAssertion;
		mLaw = getRooksAssertion(rookLaw);
	}

	/**
	 * Function creates the conjunction of all condition assertions of the rooks Law.
	 *
	 * @param rookLaw
	 *            Law for which the assertion is to be created.
	 * @param placeToAssertion
	 *            Function to map PLACE to an IPredicate assertion.
	 * @return Conjunction of the rooks assertions.
	 */
	final private IPredicate getRooksAssertion(final KingdomLaw<PLACE, LETTER> rookLaw) {
		final Set<IPredicate> rooksAssertion = new HashSet<>();
		final Set<Condition<LETTER, PLACE>> assertionConditions = rookLaw.getConditions();
		for (final Condition<LETTER, PLACE> condition : assertionConditions) {
			final IPredicate assertion = mPlaceToAssertion.apply(condition.getPlace());
			rooksAssertion.add(assertion);
		}
		return mFactory.and(rooksAssertion);
	}

	/**
	 * Adds a rooks assertion to the territories law. Intended to only be used with rooks whose territory equals
	 * mTerritory.
	 *
	 * @param rookLaw
	 *            Law for which the assertion should be added.
	 */
	public void addRooksAssertion(final KingdomLaw<PLACE, LETTER> rookLaw) {
		final IPredicate rookAssertion = getRooksAssertion(rookLaw);
		mLaw = mFactory.or(mLaw, rookAssertion);
	}

	public Territory<PLACE, LETTER> getTerritory() {
		return mTerritory;
	}

	public IPredicate getLaw() {
		return mLaw;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final TerritoryLaw<PLACE, LETTER> other = (TerritoryLaw<PLACE, LETTER>) obj;
		return mTerritory.equals(other.getTerritory());
	}

	@Override
	public int hashCode() {
		return mTerritory.hashCode();
	}
}
