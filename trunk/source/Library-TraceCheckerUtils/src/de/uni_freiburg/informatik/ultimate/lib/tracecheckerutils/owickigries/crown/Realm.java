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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Class representing Realms which are sets of Conditions whose places are pairwise not corelated. Realms are immutable.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places
 * @param <LETTER>
 *            The type of statements
 */
public final class Realm<PLACE, LETTER> {
	/**
	 * The set of conditions in realm.
	 */
	private final ImmutableSet<Condition<LETTER, PLACE>> mRealm;

	public Realm(final ImmutableSet<Condition<LETTER, PLACE>> realm) {
		assert !realm.isEmpty() : "Realm is empty";
		mRealm = realm;
	}

	private ImmutableSet<PLACE> getPlaces() {
		final ImmutableSet<PLACE> places = mRealm.stream().map(c -> c.getPlace()).collect(ImmutableSet.collector());
		return places;
	}

	private boolean placesNotCorelated(final PlacesCoRelation<PLACE> placesCoRelation) {
		final List<Condition<LETTER, PLACE>> realmConditions = new ArrayList<>(mRealm);
		for (int i = 0; i < realmConditions.size(); i++) {
			final var place1 = realmConditions.get(i).getPlace();
			for (int j = i + 1; j < realmConditions.size(); j++) {
				final var place2 = realmConditions.get(j).getPlace();
				if (placesCoRelation.getPlacesCorelation(place1, place2)) {
					assert false : "Places " + place1 + " and " + place2 + " are corelated";
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * @return copy of set of all conditions in region.
	 */
	public ImmutableSet<Condition<LETTER, PLACE>> getConditions() {
		return mRealm;
	}

	/**
	 * Creates new Realm containing the new condition and the conditions of the Realm instance the method was applied
	 * on.
	 *
	 * @param condition
	 *            Condition to be added.
	 * @return Realm containing the old conditions and the new one.
	 */
	public Realm<PLACE, LETTER> addCondition(final Condition<LETTER, PLACE> condition) {
		final var newConditions = DataStructureUtils.union(mRealm, Set.of(condition));
		return new Realm<>(ImmutableSet.of(newConditions));
	}

	/**
	 * Creates new Realm containing the new conditions and the conditions of the Realm instance the method was applied
	 * on.
	 *
	 * @param conditions
	 *            Set of conditions to be added.
	 * @return Realm containing the old conditions and the new ones.
	 */
	public Realm<PLACE, LETTER> addCondition(final Set<Condition<LETTER, PLACE>> conditions) {
		final var newConditions = DataStructureUtils.union(mRealm, conditions);
		return new Realm<>(ImmutableSet.of(newConditions));
	}

	/**
	 * Returns new Realm without the specific condition.
	 *
	 * @param condition
	 *            Condition to be removed.
	 * @return Realm without condition.
	 */
	public Realm<PLACE, LETTER> removeCondition(final Condition<PLACE, LETTER> condition) {
		final var newConditions =
				mRealm.stream().filter(cond -> !cond.equals(condition)).collect(ImmutableSet.collector());
		return new Realm<>(newConditions);
	}

	/**
	 * Returns new Realm without the specific condition.
	 *
	 * @param condition
	 *            Condition to be removed.
	 * @return Realm without condition.
	 */
	public Realm<PLACE, LETTER> removeCondition(final Set<Condition<LETTER, PLACE>> conditions) {
		final var newConditions =
				mRealm.stream().filter(cond -> !conditions.contains(cond)).collect(ImmutableSet.collector());
		return new Realm<>(newConditions);
	}

	/**
	 * Check if a condition can be added to the realm without violation the corelation restrictions.
	 *
	 * @param bp
	 *            branching process over which corelation is checked.
	 * @return true if condition is NOT corelated to all conditions in the region. TODO: itself?? / intersection or
	 *         isCorelated foreach condition in realm??
	 */
	public boolean checkAddCorelation(final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp) {
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		// set of conditions in Branching process to which the specified condition is corelated with.
		final Set<Condition<LETTER, PLACE>> coConditions = coRelation.computeCoRelatatedConditions(condition);
		// if the intersection of the coCondition and the realm is empty then the condition is not corelated
		// to any of the conditions in the realm and hence can be added.
		if (DataStructureUtils.haveEmptyIntersection(coConditions, mRealm)) {
			return true;
		}
		return false;
	}

	/**
	 * @param bp
	 *            branching process over which corelation is checked.
	 * @return true if condition is corelated to all conditions in the region. For the addition of a condition into a
	 *         territory. True AddCorelation to the realm in which the conditionn is added and true checkCorelation to
	 *         all other realms. TODO: itself?? / intersection or isCorelated foreach condition in realm??
	 */
	public boolean checkCorelation(final Condition<LETTER, PLACE> condition, final BranchingProcess<LETTER, PLACE> bp) {
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		// set of conditions in Branching process to which the specified condition is corelated with.
		final Set<Condition<LETTER, PLACE>> coConditions = coRelation.computeCoRelatatedConditions(condition);
		// if the intersection of the coCondition and the realm is empty then the condition is not corelated
		// to any of the conditions in the realm and hence can be added.
		if (coConditions.containsAll(mRealm)) {
			return true;
		}
		return false;
	}

	/**
	 * @param condition
	 * @param bp
	 * @return CoRealm with CoRelationType, Positive and Negative corelated conditions.
	 */
	public CoRealm<PLACE, LETTER> getCoRealm(final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp, final PlacesCoRelation<PLACE> placesCoRelation) {
		return new CoRealm<>(this, condition, bp, placesCoRelation);
	}

	/**
	 *
	 * @param condition
	 *            Condition whose presence in the realm is to be tested
	 * @return true if the realm contains condition
	 */
	public boolean contains(final Condition<LETTER, PLACE> condition) {
		return mRealm.contains(condition);
	}

	/**
	 * Construct Region corresponding to Realm
	 *
	 * @return Region corresponding to Realm
	 */
	public Region<PLACE> toRegion() {
		return new Region<>(getPlaces());
	}

	/**
	 * Assert that there are no two conditions whose corresponding places are corelated
	 *
	 * @param placesCoRelation
	 *            Contains the information about the corelation of the Places.
	 */
	public boolean validityAssertion(final PlacesCoRelation<PLACE> placesCoRelation) {
		final boolean valid = placesNotCorelated(placesCoRelation);
		assert valid : "There are Conditions with co-related Places in the Realm";
		return valid;
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
		final Realm<PLACE, LETTER> other = (Realm<PLACE, LETTER>) obj;
		return mRealm.equals(other.getConditions());
	}

	@Override
	public int hashCode() {
		return mRealm.hashCode();
	}

	@Override
	public String toString() {
		return mRealm.toString();
	}
}
