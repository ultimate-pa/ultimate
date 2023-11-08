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

public final class CoRealm<PLACE, LETTER> {

	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final Realm<PLACE, LETTER> mRealm;
	private final Condition<LETTER, PLACE> mCondition;

	/**
	 * Subset of Realm's condition that are corelated to specified condition;
	 */
	private final Set<Condition<LETTER, PLACE>> mPosRealm;

	/**
	 * Subset of Realm's condition that are not corelated to mCondition;
	 */
	private final Set<Condition<LETTER, PLACE>> mNegRealm;

	/**
	 * Corelation type of condition wrt. Realm.
	 */
	private final CoRelationType mCoRel;

	public CoRealm(final Realm<PLACE, LETTER> realm, final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mRealm = realm;
		mCondition = condition;
		mPosRealm = getPosRealm();
		mNegRealm = DataStructureUtils.difference(mRealm.getConditions(), mPosRealm);
		mCoRel = getCoRelType();
	}

	/**
	 * @return Subset of Realm's conditions corelated to CoRealm' condition.
	 */
	private final Set<Condition<LETTER, PLACE>> getPosRealm() {
		return DataStructureUtils.intersection(mRealm.getConditions(),
				mCoRelation.computeCoRelatatedConditions(mCondition));
	}

	/**
	 * @return CoRelation type of Realm wrt. specified condition.
	 */

	private final CoRelationType getCoRelType() {
		if (mRealm.getConditions().equals(mPosRealm)) {
			return CoRelationType.POSITIVE;
		} else if (mRealm.getConditions().equals(mNegRealm)) {
			return CoRelationType.NEGATIVE;
		} else {
			return CoRelationType.PARTIAL;
		}

	}

	public final CoRelationType getCoRelation() {
		return mCoRel;
	}

}
