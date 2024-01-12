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

final class CoLaw<PLACE, LETTER> {

	private final ICoRelation<LETTER, PLACE> mCoRelation;
	private final KingdomLaw<PLACE, LETTER> mLaw;
	private final Condition<LETTER, PLACE> mCondition;

	/**
	 * Subset of Law's condition that are corelated to specified condition;
	 */
	private final Set<Condition<LETTER, PLACE>> mPosLaw;

	/**
	 * Corelation type of condition wrt. Law.
	 */
	private final CoRelationType mCoRel;

	// TODO: keep both classes (CoRealm and CoLaw) or merge into one?
	// issue: neg & partial corelationtype conflict.(one for each?)
	public CoLaw(final KingdomLaw<PLACE, LETTER> law, final Condition<LETTER, PLACE> condition,
			final BranchingProcess<LETTER, PLACE> bp) {
		mCoRelation = bp.getCoRelation();
		mLaw = law;
		mCondition = condition;
		mPosLaw = getPosLaw();
		mCoRel = getCoRelType();
	}

	/**
	 * @return Subset of Law's conditions corelated to CoLaw's condition.
	 */
	private Set<Condition<LETTER, PLACE>> getPosLaw() {
		return mLaw.getConditions().stream().filter(c -> mCoRelation.isInCoRelation(c, mCondition))
				.collect(Collectors.toSet());
	}

	/**
	 * @return CoRelation type of Law wrt. specified condition.
	 */
	private CoRelationType getCoRelType() {
		if (mLaw.getConditions().contains(mCondition)) {
			return CoRelationType.CONTAINS;
		}
		if (mPosLaw.isEmpty()) {
			return CoRelationType.NEGATIVE;
		} else if (mPosLaw.size() == mLaw.getConditions().size()) {
			return CoRelationType.POSITIVE;
		} else {
			return CoRelationType.PARTIAL;
		}
	}

	public CoRelationType getCoRelation() {
		return mCoRel;
	}
}
