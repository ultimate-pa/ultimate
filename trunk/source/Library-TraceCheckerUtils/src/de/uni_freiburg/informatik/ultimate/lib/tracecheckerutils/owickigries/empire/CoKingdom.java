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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class CoKingdom<PLACE, LETTER> {

	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final Kingdom<PLACE, LETTER> mKingdom;
	private final Condition<LETTER, PLACE> mCondition;

	/**
	 * Subset of Realms in Kingdom that have positive corelation wrt. specified condition;
	 */
	public Set<Realm<PLACE, LETTER>> mPosKingdom;

	/**
	 * Subset of Realms in Kingdom that have partial corelation wrt. specified condition;
	 */
	public Set<Realm<PLACE, LETTER>> mParKingdom;

	/**
	 * Subset of Realms in Kigmdom that are have negative corelation wrt. specified condition
	 */
	public Set<Realm<PLACE, LETTER>> mNegKingdom;

	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;

	private final boolean mConflictFree;

	public CoKingdom(final Kingdom<PLACE, LETTER> kingdom, final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mKingdom = kingdom;
		mCondition = condition;
		getCoKingdoms(bp);
		mCoRel = getCoRelType();
		mConflictFree = getConflictFreedom(); // TODO: complete conflict freedom computation
	}

	/**
	 * Divide all Realms in Kingdom according to their realm corelation type.
	 *
	 * @param bp
	 */
	private void getCoKingdoms(final BranchingProcess<LETTER, PLACE> bp) {
		for (final Realm<PLACE, LETTER> realm : mKingdom.getRealms()) {
			final CoRealm<PLACE, LETTER> coRealm = new CoRealm(realm, mCondition, bp);
			switch (coRealm.getCoRelation()) {
			case POSITIVE:
				mPosKingdom.add(realm);
				break;
			case NEGATIVE:
				mNegKingdom.add(realm);
				break;
			default:
				mParKingdom.add(realm);
			}
		}
	}

	/**
	 * @return CoRelation type pf Kingdom according to the corelation time of the kingdom's realms.
	 */
	private CoRelationType getCoRelType() {
		if (mKingdom.equals(mPosKingdom)) {
			return CoRelationType.POSITIVE;
		} else if (mNegKingdom.size() == 1
				&& mPosKingdom.containsAll(DataStructureUtils.difference(mKingdom.getRealms(), mNegKingdom))) {
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

	private boolean getConflictFreedom() {
		return true;
	}

	public boolean getConflictFree() {
		return mConflictFree;
	}

	public Set<Realm<PLACE, LETTER>> getNegKingdom() {
		return mNegKingdom;
	}

	public Set<Realm<PLACE, LETTER>> getPosKingdom() {
		return mPosKingdom;
	}
}
