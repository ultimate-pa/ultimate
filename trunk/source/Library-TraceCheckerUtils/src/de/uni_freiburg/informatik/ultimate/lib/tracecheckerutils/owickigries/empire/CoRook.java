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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class CoRook<PLACE, LETTER> {

	private final Rook<PLACE, LETTER> mRook;
	private final Condition<LETTER, PLACE> mCondition;
	private final CoKingdom<PLACE, LETTER> mCoKingdom;
	private final CoLaw<PLACE, LETTER> mCoLaw;
	private final ColonizationType mColonization;
	private final LegislationType mLegislation;
	private final boolean mIsColonizer;

	public CoRook(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook,
			final BranchingProcess<LETTER, PLACE> bp, final boolean isColonizer,
			final PlacesCoRelation<PLACE, LETTER> placesCoRelation) {
		mRook = rook;
		mCondition = condition;
		mIsColonizer = isColonizer;
		mCoKingdom = new CoKingdom<>(mRook.getKingdom(), condition, bp, placesCoRelation);
		mCoLaw = new CoLaw<>(mRook.getLaw(), condition, bp);
		mColonization = getColonizationStrategy();
		mLegislation = getLegislationStrategy();
	}

	private ColonizationType getColonizationStrategy() {
		if (mIsColonizer) {
			if (mCoKingdom.getCoRelation() == CoRelationType.POSITIVE
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return ColonizationType.EXPANSION;
			} else if (mCoKingdom.getCoRelation() == CoRelationType.PARTIAL
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				if (mCoKingdom.getConflictFree()) {
					return ColonizationType.IMMIGRATION;
				} else {
					return ColonizationType.FOUNDATION;
				}
			} else {
				return ColonizationType.DEFEAT;
			}
		}
		return ColonizationType.NULL;
	}

	private LegislationType getLegislationStrategy() {
		if (!mIsColonizer) {
			if (mCoKingdom.getCoRelation() == CoRelationType.POSITIVE
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return LegislationType.APPROVAL;
			} else if (mCoKingdom.getCoRelation() == CoRelationType.POSITIVE
					&& mCoLaw.getCoRelation() == CoRelationType.NEGATIVE) {
				return LegislationType.ENACTMENT;
			} else if (mCoKingdom.getCoRelation() == CoRelationType.PARTIAL
					&& mCoLaw.getCoRelation() == CoRelationType.POSITIVE) {
				return LegislationType.RATIFICATION;
			} else {
				return LegislationType.REJECTION;
			}
		}
		return LegislationType.NULL;
	}

	public LegislationType getLegislation() {
		return mLegislation;
	}

	public ColonizationType getColonization() {
		return mColonization;
	}

	public Rook<PLACE, LETTER> getRook() {
		return mRook;
	}

	public Condition<LETTER, PLACE> getCondition() {
		return mCondition;
	}

	public CoKingdom<PLACE, LETTER> getCoKingdom() {
		return mCoKingdom;
	}

	public CoLaw<PLACE, LETTER> getCoLaw() {
		return mCoLaw;
	}
}
