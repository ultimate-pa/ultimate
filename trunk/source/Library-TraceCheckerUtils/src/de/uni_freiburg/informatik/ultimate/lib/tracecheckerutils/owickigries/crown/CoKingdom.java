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

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

final class CoKingdom<PLACE, LETTER> {

	private final Kingdom<PLACE, LETTER> mKingdom;
	private final Condition<LETTER, PLACE> mCondition;

	/**
	 * Subset of Realms in Kingdom that have positive corelation wrt. specified condition;
	 */
	private Set<Realm<PLACE, LETTER>> mPosKingdom;

	/**
	 * Subset of Realms in Kingdom that have partial corelation wrt. specified condition;
	 */
	private Set<Realm<PLACE, LETTER>> mParKingdom;

	/**
	 * Subset of coRealms which correspond to Realms in Kingdom that have partial corelation wrt. specified condition;
	 */
	private Set<CoRealm<PLACE, LETTER>> mParCoRealms;

	/**
	 * Subset of Realms in Kigmdom that are have negative corelation wrt. specified condition
	 */
	private Set<Realm<PLACE, LETTER>> mNegKingdom;

	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;

	/**
	 * Calculates the different corelation and conflict sets and sets them.
	 *
	 * @param kingdom
	 *            Kingdom of which the corelation to condition shall be checked
	 * @param condition
	 *            Condition for checking the corelation to kingdom
	 * @param bp
	 *            Complete finite prefix of the refined Petri net
	 * @param placesCoRelation
	 *            Objects which stores the corelation for the original Places of bp
	 */
	public CoKingdom(final Kingdom<PLACE, LETTER> kingdom, final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp, final PlacesCoRelation<PLACE> placesCoRelation) {
		mKingdom = kingdom;
		mCondition = condition;
		final boolean success = getCoKingdoms(bp, placesCoRelation);
		mCoRel = getCoRelType(success);
	}

	/**
	 * Divide all Realms in Kingdom according to their realm corelation type.
	 *
	 * @param bp
	 */
	private boolean getCoKingdoms(final BranchingProcess<LETTER, PLACE> bp,
			final PlacesCoRelation<PLACE> placesCoRelation) {
		mPosKingdom = new HashSet<>();
		mNegKingdom = new HashSet<>();
		mParKingdom = new HashSet<>();
		mParCoRealms = new HashSet<>();
		for (final Realm<PLACE, LETTER> realm : mKingdom.getRealms()) {
			if (realm.contains(mCondition)) {
				return false;
			}
			final CoRealm<PLACE, LETTER> coRealm = new CoRealm<>(realm, mCondition, bp, placesCoRelation);
			switch (coRealm.getCoRelation()) {
			case POSITIVE:
				mPosKingdom.add(realm);
				break;
			case NEGATIVE:
				mNegKingdom.add(realm);
				break;
			default:
				mParKingdom.add(realm);
				mParCoRealms.add(coRealm);
			}
		}
		return true;
	}

	/**
	 * @return CoRelation type pf Kingdom according to the corelation time of the kingdom's realms.
	 */
	private CoRelationType getCoRelType(final boolean success) {
		if (!success) {
			return CoRelationType.CONTAINS;
		}
		if (mKingdom.getRealms().size() == mPosKingdom.size()) {
			return CoRelationType.POSITIVE;
		} else if (mNegKingdom.size() == 1
				&& mPosKingdom.containsAll(DataStructureUtils.difference(mKingdom.getRealms(), mNegKingdom))
				&& !mPosKingdom.isEmpty()) {
			return CoRelationType.PARTIAL;
		} else if (mParKingdom.size() == 1
				&& mPosKingdom.containsAll(DataStructureUtils.difference(mKingdom.getRealms(), mParKingdom))) {
			return CoRelationType.DIVERGENT;
		} else {
			return CoRelationType.NEGATIVE;
		}
	}

	public CoRelationType getCoRelation() {
		return mCoRel;
	}

	public Set<Realm<PLACE, LETTER>> getNegKingdom() {
		return mNegKingdom;
	}

	public Set<Realm<PLACE, LETTER>> getPosKingdom() {
		return mPosKingdom;
	}

	public Set<Realm<PLACE, LETTER>> getParKingdom() {
		return mParKingdom;
	}

	public Set<CoRealm<PLACE, LETTER>> getParCoRealms() {
		return mParCoRealms;
	}

	public Set<Condition<LETTER, PLACE>> getConflictFreeConditions(final BranchingProcess<LETTER, PLACE> bp,
			final PlacesCoRelation<PLACE> placesCoRelation) {
		if (mNegKingdom.isEmpty()) {
			return Collections.emptySet();
		}
		final Realm<PLACE, LETTER> negativeRealm = DataStructureUtils.getOneAndOnly(mNegKingdom, "negative kingdom");
		final CoRealm<PLACE, LETTER> negativeCoRealm = negativeRealm.getCoRealm(mCondition, bp, placesCoRelation);
		return negativeCoRealm.getConflictFreeSet();
	}
}
