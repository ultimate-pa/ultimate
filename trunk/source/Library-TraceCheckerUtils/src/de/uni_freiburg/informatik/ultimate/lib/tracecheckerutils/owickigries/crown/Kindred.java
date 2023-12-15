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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

final class Kindred<PLACE, LETTER> {
	private final Set<Rook<PLACE, LETTER>> mCrownRooks;
	private final HashRelation<Rook<PLACE, LETTER>, SubterrElement<LETTER, PLACE>> mSubterritories;
	private final HashRelation<Marking<PLACE>, Rook<PLACE, LETTER>> mMarkingToRook;

	public Kindred(final Set<Rook<PLACE, LETTER>> crownRooks) {
		mCrownRooks = crownRooks;
		mSubterritories = computeSubterritories();
		mMarkingToRook = computeMarkingToRook();
	}

	private HashRelation<Rook<PLACE, LETTER>, SubterrElement<LETTER, PLACE>> computeSubterritories() {
		final HashRelation<Rook<PLACE, LETTER>, SubterrElement<LETTER, PLACE>> subterritories = new HashRelation<>();
		for (final Rook<PLACE, LETTER> rook : mCrownRooks) {
			final Set<SubterrElement<LETTER, PLACE>> subterrElements = rook.getSubterritory();
			subterritories.addAllPairs(rook, subterrElements);
		}
		return subterritories;
	}

	private HashRelation<Marking<PLACE>, Rook<PLACE, LETTER>> computeMarkingToRook() {
		final HashRelation<Marking<PLACE>, Rook<PLACE, LETTER>> markingToRook = new HashRelation<>();
		for (final Rook<PLACE, LETTER> rook : mSubterritories.getDomain()) {
			for (final SubterrElement<LETTER, PLACE> subterrElement : mSubterritories.getImage(rook)) {
				markingToRook.addPair(subterrElement.getMarking(), rook);
			}
		}
		return markingToRook;
	}

	private boolean isKindredRookPair(final Set<Set<Condition<LETTER, PLACE>>> rook1Subkingdom,
			final Set<Set<Condition<LETTER, PLACE>>> rook2Subkingdom) {
		if (rook1Subkingdom.equals(rook2Subkingdom)) {
			return false;
		}
		return true;
	}

	private boolean isKindredMarking(final Marking<PLACE> marking, final Rook<PLACE, LETTER> rook,
			final Set<SubterrElement<LETTER, PLACE>> rookSubterr) {
		final Set<Set<Condition<LETTER, PLACE>>> rookSubkingdom = rook.getSubkingdom(rookSubterr, marking);
		for (final Rook<PLACE, LETTER> kindredRook : mMarkingToRook.getImage(marking)) {
			if (rook.equals(kindredRook)) {
				continue;
			}
			final Set<Set<Condition<LETTER, PLACE>>> kindredRookSubkingdom =
					kindredRook.getSubkingdom(mSubterritories.getImage(kindredRook), marking);
			if (isKindredRookPair(rookSubkingdom, kindredRookSubkingdom)) {
				return true;
			}
		}
		return false;
	}

	private Set<Condition<LETTER, PLACE>> getSubkingdomConditions(final Set<Set<Condition<LETTER, PLACE>>> subkingdom) {
		Set<Condition<LETTER, PLACE>> subkingdomConditions = new HashSet<>();
		for (final Set<Condition<LETTER, PLACE>> coSet : subkingdom) {
			subkingdomConditions = DataStructureUtils.union(subkingdomConditions, coSet);
		}
		return subkingdomConditions;
	}

	/**
	 * Selects all markings of rook which are also contained in another rook of mCrown but have different subkingdoms
	 * than the marking in rook.
	 *
	 * @param rook
	 *            Rook for which the kindred markings should be computed.
	 * @return Set of kindred markings of rook.
	 */
	public Set<Marking<PLACE>> getKindredMarkings(final Rook<PLACE, LETTER> rook) {
		final Set<Marking<PLACE>> kindredMarkings = new HashSet<>();
		final Set<SubterrElement<LETTER, PLACE>> rookSubterr = mSubterritories.getImage(rook);
		for (final SubterrElement<LETTER, PLACE> subterrElement : rookSubterr) {
			final Marking<PLACE> marking = subterrElement.getMarking();
			if (isKindredMarking(marking, rook, rookSubterr)) {
				kindredMarkings.add(marking);
			}
		}
		return kindredMarkings;
	}

	/**
	 * Selects all rooks which contain marking if another rook exists which also contains marking but has another
	 * subkingdom for it.
	 *
	 * @param marking
	 *            The corresponding marking for which we want to compute the kindred rooks.
	 * @return Set of kindred rooks corresponding to marking.
	 */
	public Set<Rook<PLACE, LETTER>> getKindredRooks(final Marking<PLACE> marking) {
		final Set<Rook<PLACE, LETTER>> markingRooks = mMarkingToRook.getImage(marking);
		final Set<Rook<PLACE, LETTER>> kindredRooks = new HashSet<>();
		for (final Rook<PLACE, LETTER> rook1 : markingRooks) {
			final Set<Set<Condition<LETTER, PLACE>>> r1Subkingdom =
					rook1.getSubkingdom(mSubterritories.getImage(rook1), marking);
			for (final Rook<PLACE, LETTER> rook2 : markingRooks) {
				if (rook1.equals(rook2) || (kindredRooks.contains(rook1) && kindredRooks.contains(rook2))) {
					continue;
				}
				final Set<Set<Condition<LETTER, PLACE>>> r2Subkingdom =
						rook2.getSubkingdom(mSubterritories.getImage(rook2), marking);
				if (isKindredRookPair(r1Subkingdom, r2Subkingdom)) {
					kindredRooks.add(rook1);
					kindredRooks.add(rook2);
				}

			}
		}
		return kindredRooks;
	}

	/**
	 * Determines all kindred conditions in rook wrt. to marking.
	 *
	 * @param marking
	 *            Corresponding marking
	 * @param rook
	 *            Rook for which we want do determine the conditions.
	 * @return Set containing all kindred conditions wrt. to marking and rook.
	 */
	public Set<Condition<LETTER, PLACE>> getKindredConditions(final Marking<PLACE> marking,
			final Rook<PLACE, LETTER> rook) {
		final Set<Condition<LETTER, PLACE>> kindredConditions = new HashSet<>();
		final Set<Set<Condition<LETTER, PLACE>>> rookSubkingdom =
				rook.getSubkingdom(mSubterritories.getImage(rook), marking);
		final Set<Rook<PLACE, LETTER>> kindredRooks = getKindredRooks(marking);
		for (final Rook<PLACE, LETTER> kindredRook : kindredRooks) {
			final Set<Set<Condition<LETTER, PLACE>>> kindredRookSubkingdom =
					kindredRook.getSubkingdom(mSubterritories.getImage(kindredRook), marking);
			for (final Set<Condition<LETTER, PLACE>> coSet1 : rookSubkingdom) {
				for (final Set<Condition<LETTER, PLACE>> coSet2 : kindredRookSubkingdom) {
					kindredConditions.addAll(DataStructureUtils.difference(coSet1, coSet2));
				}
			}
		}
		return kindredConditions;
	}

	/**
	 * Determines the union of the kindred conditions for the rook wrt. to each marking
	 *
	 * @param markings
	 *            Set containing all markings for which the kindred conditions should be determined.
	 * @param rook
	 *            Corresponding rook
	 * @return Set containing the union of the kindred conditions.
	 */
	public Set<Condition<LETTER, PLACE>> getKindredConditions(final Set<Marking<PLACE>> markings,
			final Rook<PLACE, LETTER> rook) {
		final Set<Condition<LETTER, PLACE>> kindredConditions = new HashSet<>();
		for (final Marking<PLACE> marking : markings) {
			kindredConditions.addAll(getKindredConditions(marking, rook));
		}
		return kindredConditions;
	}

	/**
	 * Determines all realms in rook which have common conditions with the Set conditions.
	 *
	 * @param conditions
	 *            Set containing all conditions we want to calculate the kindred realms with.
	 * @param rook
	 *            Corresponding rook.
	 * @return Set of kindred realms.
	 */
	public Set<Realm<PLACE, LETTER>> getKindredRealms(final Set<Condition<LETTER, PLACE>> conditions,
			final Rook<PLACE, LETTER> rook) {
		final Set<Realm<PLACE, LETTER>> kindredRealms = new HashSet<>();
		for (final Realm<PLACE, LETTER> realm : rook.getKingdom().getRealms()) {
			final Set<Condition<LETTER, PLACE>> intersection =
					DataStructureUtils.intersection(realm.getConditions(), conditions);
			if (!intersection.isEmpty()) {
				kindredRealms.add(realm);
			}
		}
		return kindredRealms;
	}
}
