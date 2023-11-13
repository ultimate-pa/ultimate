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

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class Rook<PLACE, LETTER> {

	/**
	 * Kingdom element (region of conditions)
	 */
	private final Kingdom<PLACE, LETTER> mKingdom;

	/**
	 * Law element (set of assertion conditions)
	 */
	private final KingdomLaw<PLACE, LETTER> mLaw;

	public Rook(final Kingdom kingdom, final KingdomLaw<PLACE, LETTER> law) {
		mKingdom = kingdom;
		mLaw = law;
	}

	/**
	 * Add a new town realm (only with specified condition) to Kingdom.
	 *
	 * @param cond
	 */
	public void expansion(final Condition<LETTER, PLACE> condition) {
		final Realm<PLACE, LETTER> realm = new Realm<>(DataStructureUtils.toSet(condition));
		mKingdom.addRealm(realm);
	}

	/**
	 * Adds the condition to the specified existing realm of the rook's Kingdom.
	 *
	 * @param condition
	 * @param realm
	 * @return true if condition is added, false if realm is not found in Kingdom. TODO: Kindred cases...
	 */
	public boolean immigration(final Condition<LETTER, PLACE> condition, final Realm<PLACE, LETTER> realm) {
		if (mKingdom.removeRealm(realm)) {
			realm.addCondition(condition);
			mKingdom.addRealm(realm);
			return true;
		}
		return false;
	}

	/**
	 * Add new assertion condition into the Rook's law set
	 *
	 * @param condition
	 */
	public void approval(final Condition<LETTER, PLACE> condition) {
		mLaw.addCondition(condition);
	}

	/**
	 * TODO: Kindred check and immigration TODO: Coset/rook check
	 */

	public Set<Collection<Condition<LETTER, PLACE>>> census() {
		final Set<Collection<Condition<LETTER, PLACE>>> coSets = new HashSet<>();
		for (final Realm<PLACE, LETTER> realm : mKingdom.getRealms()) {
			coSets.add(DataStructureUtils.union(realm.getConditions(), mLaw.getConditions()));
		}
		return coSets;
	}

	/**
	 * TODO: compute if it is maximal/cut.??
	 *
	 * @param coSet
	 * @return true if coSet is a cut/maximal coset.
	 */
	public boolean isCut(final Collection<Condition<LETTER, PLACE>> coSet) {
		return true;
	}

	public Kingdom<PLACE, LETTER> getKingdom() {
		return mKingdom;
	}

	public KingdomLaw<PLACE, LETTER> getLaw() {
		return mLaw;
	}

	public Set<SubterrElement<LETTER, PLACE>> getSubterritory() {
		final Set<Set<Condition<LETTER, PLACE>>> treaty = getKingdom().getTreaty();
		final Set<SubterrElement<LETTER, PLACE>> subterr = new HashSet<>();
		for (final Set<Condition<LETTER, PLACE>> set : treaty) {
			final SubterrElement<LETTER, PLACE> subterrElement = new SubterrElement<>(set);
			subterr.add(subterrElement);
		}
		return subterr;
	}

	/**
	 *
	 * @param subterr
	 *            A subterritory of a rook.
	 * @param marking
	 *            The marking we want to get all corresponding cosets of.
	 * @return All cosets in subterr which label to the marking.
	 */
	public Set<Set<Condition<LETTER, PLACE>>> getSubkingdom(final Set<SubterrElement<LETTER, PLACE>> subterr,
			final Set<PLACE> marking) {
		final Set<Set<Condition<LETTER, PLACE>>> subkingdom = new HashSet<>();
		for (final SubterrElement<LETTER, PLACE> subterrElement : subterr) {
			if (subterrElement.getMarking().containsAll(marking)) {
				subkingdom.add(subterrElement.mCoSet);
			}
		}
		return subkingdom;
	}
}
