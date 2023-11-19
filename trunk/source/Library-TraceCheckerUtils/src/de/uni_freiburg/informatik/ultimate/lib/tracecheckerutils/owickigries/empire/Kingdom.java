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

public final class Kingdom<PLACE, LETTER> {
	/**
	 * The set of realms in Kingdom.
	 */
	private final Set<Realm<PLACE, LETTER>> mKingdom;

	public Kingdom(final Set<Realm<PLACE, LETTER>> kingdom) {
		mKingdom = kingdom;
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
		return mKingdom;
	}

	/**
	 * Adds the specified realm into the set of realms in the kingdom.
	 *
	 * @param realm
	 */
	public void addRealm(final Realm<PLACE, LETTER> realm) {
		mKingdom.add(realm);
	}

	/**
	 * Add the specified set of realms into the Kingdom.
	 *
	 * @param realms
	 */
	public void addRealm(final Set<Realm<PLACE, LETTER>> realms) {
		mKingdom.addAll(realms);
	}

	/**
	 * Remove the specified realm from Kingdom.
	 *
	 * @param realm
	 */
	public boolean removeRealm(final Realm<PLACE, LETTER> realm) {
		if (mKingdom.contains(realm)) {
			mKingdom.remove(realm);
			return true;
		}
		return false;
	}

	public boolean removeRealm(final Set<Realm<PLACE, LETTER>> realms) {
		boolean removalSuccess = true;
		for (final Realm<PLACE, LETTER> realm : realms) {
			if (!removeRealm(realm)) {
				removalSuccess = false;
			}
		}
		return removalSuccess;
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
		final Set<Realm<PLACE, LETTER>> kingdomRealms = new HashSet<>(getRealms());
		getAllCosets(kingdomRealms, new HashSet<>(), treatySet);
		return treatySet;
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
