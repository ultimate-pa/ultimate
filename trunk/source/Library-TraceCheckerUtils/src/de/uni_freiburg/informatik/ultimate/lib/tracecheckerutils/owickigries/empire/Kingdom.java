/*
 * Copyright (C) 2020 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Class Kingdom represents sets of Realms. To be a valid Kingdom, it is non-empty, all Realms have to be disjoint and
 * further all subsets in its treaty are co-sets. Kingdoms are immutable.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 * @param <LETTER>
 */
public final class Kingdom<PLACE, LETTER> {
	/**
	 * The set of realms in Kingdom.
	 */
	private final Set<Realm<PLACE, LETTER>> mKingdom;

	public Kingdom(final Set<Realm<PLACE, LETTER>> kingdom) {
		mKingdom = new HashSet<>(kingdom);
	}

	private void getAllCosets(final Set<Realm<PLACE, LETTER>> remainingKingdom,
			final Set<Condition<LETTER, PLACE>> currentCoset, final Set<Set<Condition<LETTER, PLACE>>> treaty) {
		if (remainingKingdom.isEmpty()) {
			treaty.add(new HashSet<>(currentCoset));
			return;
		}
		final Realm<PLACE, LETTER> currentRealm = remainingKingdom.iterator().next();
		remainingKingdom.remove(currentRealm);

		for (final Condition<LETTER, PLACE> condition : currentRealm.getConditions()) {
			currentCoset.add(condition);
			getAllCosets(new HashSet<>(remainingKingdom), new HashSet<>(currentCoset), treaty);
			currentCoset.remove(condition);
		}
	}

	/**
	 * @return Set of realms in Kingdom.
	 */
	public Set<Realm<PLACE, LETTER>> getRealms() {
		return new HashSet<>(mKingdom);
	}

	/**
	 * Returns new kingdom with the realm added to it.
	 *
	 * @param realm
	 *            Realm to be added into the kingdom
	 * @return New kingdom with realm added into it.
	 */
	public Kingdom<PLACE, LETTER> addRealm(final Realm<PLACE, LETTER> realm) {
		final Set<Realm<PLACE, LETTER>> realms = getRealms();
		realms.add(realm);
		return new Kingdom<>(realms);
	}

	/**
	 * Returns new kingdom with the realms added to it.
	 *
	 * @param realms
	 *            Realms to be added into the kingdom
	 * @return New kingdom with realms added into it.
	 */
	public Kingdom<PLACE, LETTER> addRealm(final Set<Realm<PLACE, LETTER>> realms) {
		final Set<Realm<PLACE, LETTER>> kingdomRealms = getRealms();
		kingdomRealms.addAll(realms);
		return new Kingdom<>(kingdomRealms);
	}

	/**
	 * Return new kingdom without the specific realm.
	 *
	 * @param realm
	 *            Realm to be removed
	 * @return New kingdom without realm
	 */
	public Kingdom<PLACE, LETTER> removeRealm(final Realm<PLACE, LETTER> realm) {
		if (mKingdom.contains(realm)) {
			final Set<Realm<PLACE, LETTER>> kingdomRealms = getRealms();
			kingdomRealms.remove(realm);
			return new Kingdom<>(kingdomRealms);
		}
		return new Kingdom<>(mKingdom);
	}

	/**
	 * Return new kingdom without the specific realms.
	 *
	 * @param realms
	 *            Realms to be removed
	 * @return New kingdom without realms
	 */
	public Kingdom<PLACE, LETTER> removeRealm(final Set<Realm<PLACE, LETTER>> realms) {
		final Set<Realm<PLACE, LETTER>> kingdomRealms = getRealms();
		kingdomRealms.removeAll(realms);
		return new Kingdom<>(kingdomRealms);
	}

	/**
	 * @param condition
	 * @param bp
	 * @return CoKingdom with corelation type and Kingdom's realms subsets by the corelation type of the realm wrt.
	 *         condition.
	 */
	public CoKingdom<PLACE, LETTER> getCoKingdom(final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp, final PlacesCoRelation<PLACE, LETTER> placesCoRelation) {
		return new CoKingdom<>(this, condition, bp, placesCoRelation);
	}

	/**
	 * Calculate the treaty by creating a set of cosets picking one condition per realm.
	 *
	 * @return Treaty of the Kingdom.
	 */
	public Set<Set<Condition<LETTER, PLACE>>> getTreaty() {
		final Set<Set<Condition<LETTER, PLACE>>> treatySet = new HashSet<>();
		final Set<Realm<PLACE, LETTER>> kingdomRealms = getRealms();
		getAllCosets(kingdomRealms, new HashSet<>(), treatySet);
		return treatySet;
	}

	/**
	 * Assert that all realms in the Kingdom are valid, that the kingdom is not empty and that the realms in the kingdom
	 * are disjoint.
	 *
	 * @param placesCoRelation
	 *            Contains the information about the corelation of the Places.
	 */
	public void validityAssertion(final PlacesCoRelation<PLACE, LETTER> placesCoRelation) {
		for (final Realm<PLACE, LETTER> realm : mKingdom) {
			realm.validityAssertion(placesCoRelation);
		}
		assert !mKingdom.isEmpty() : "There is an empty Kingdom";
		boolean foundAny = false;
		Set<Condition<LETTER, PLACE>> intersectionConditions = null;
		for (final Realm<PLACE, LETTER> realm : mKingdom) {
			if (!foundAny) {
				foundAny = true;
				intersectionConditions = realm.getConditions();
				continue;
			}
			intersectionConditions = DataStructureUtils.intersection(intersectionConditions, realm.getConditions());
			assert intersectionConditions.isEmpty() : "Kingdoms Realms are not disjoint";
		}
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
		final Kingdom<PLACE, LETTER> other = (Kingdom<PLACE, LETTER>) obj;
		return mKingdom.equals(other.getRealms());
	}

	@Override
	public int hashCode() {
		return mKingdom.hashCode();
	}
}
