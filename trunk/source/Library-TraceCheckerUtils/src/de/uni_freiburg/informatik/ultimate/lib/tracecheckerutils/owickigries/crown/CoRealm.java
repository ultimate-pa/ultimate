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

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;

final class CoRealm<PLACE, LETTER> {

	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final Realm<PLACE, LETTER> mRealm;
	private final Condition<LETTER, PLACE> mCondition;

	/**
	 * Subset of Realm's condition that are not corelated to mCondition;
	 */
	private final Set<Condition<LETTER, PLACE>> mNegRealm;

	private final Set<Condition<LETTER, PLACE>> mConflictFreeConditions;

	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;

	private final ConflictType mConflictType;

	public CoRealm(final Realm<PLACE, LETTER> realm, final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp, final PlacesCoRelation<PLACE> placesCoRelation) {
		mCoRelation = bp.getCoRelation();
		mRealm = realm;
		mCondition = condition;
		mNegRealm = getNegRealm();
		mCoRel = getCoRelType();
		mConflictFreeConditions = getConflicFreeConditions(placesCoRelation);
		mConflictType = getConflictType();
	}

	/**
	 * @return Subset of Realm's conditions not corelated to CoRealm's condition.
	 */
	private Set<Condition<LETTER, PLACE>> getNegRealm() {
		return mRealm.getConditions().stream().filter(c -> !mCoRelation.isInCoRelation(c, mCondition))
				.collect(Collectors.toSet());
	}

	/**
	 * @param placesCoRelation
	 *            Object which was initialized with the bp we want to create a proof for
	 * @return Subset of Realm's conditions for which their places are not corelated to the place of condition.
	 */
	private Set<Condition<LETTER, PLACE>> getConflicFreeConditions(final PlacesCoRelation<PLACE> placesCoRelation) {
		final PLACE originalPlace = mCondition.getPlace();
		return mRealm.getConditions().stream()
				.filter(c -> !placesCoRelation.getPlacesCorelation(originalPlace, c.getPlace()))
				.collect(Collectors.toSet());
	}

	/**
	 *
	 * @return The conflict type of the realm wrt. condition
	 */
	private ConflictType getConflictType() {
		if (mRealm.getConditions().size() == mConflictFreeConditions.size()) {
			return ConflictType.CONFLICT_FREE;
		}
		return ConflictType.CONFLICTING;
	}

	/**
	 * @return CoRelation type of Realm wrt. specified condition.
	 */

	private CoRelationType getCoRelType() {
		final int realmSize = mRealm.getConditions().size();
		if (mNegRealm.isEmpty()) {
			return CoRelationType.POSITIVE;
		} else if (realmSize == mNegRealm.size()) {
			return CoRelationType.NEGATIVE;
		} else {
			return CoRelationType.PARTIAL;
		}

	}

	public CoRelationType getCoRelation() {
		return mCoRel;
	}

	public ConflictType getConflict() {
		return mConflictType;
	}

	public Set<Condition<LETTER, PLACE>> getConflictFreeSet() {
		return mConflictFreeConditions;
	}

	public Realm<PLACE, LETTER> getRealm() {
		return mRealm;
	}

	public Set<Condition<LETTER, PLACE>> getNegConditions() {
		return mNegRealm;
	}

}
