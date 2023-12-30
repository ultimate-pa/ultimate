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

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Class represents Rooks which are Kingdom and Law pairs. Rooks are immutable.
 *
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

	public Rook(final Kingdom<PLACE, LETTER> kingdom, final KingdomLaw<PLACE, LETTER> law) {
		mKingdom = kingdom;
		mLaw = law;
	}

	private boolean isCut(final Set<Condition<LETTER, PLACE>> possibleCut, final BranchingProcess<LETTER, PLACE> bp) {
		final Set<Condition<LETTER, PLACE>> allConditions = new HashSet<>(bp.getConditions());
		final Set<Condition<LETTER, PLACE>> missingConditions =
				DataStructureUtils.difference(allConditions, possibleCut);
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		// Check for all conditions not in coSet if any is corelated to all conditions in coSet
		for (final Condition<LETTER, PLACE> condition : missingConditions) {
			final Set<Condition<LETTER, PLACE>> coConditions = coRelation.computeCoRelatatedConditions(condition);
			if (coConditions.containsAll(possibleCut)) {
				// If condition is corelated to all elements of coSet, it is not a cut
				return false;
			}
		}
		return true;
	}

	private Realm<PLACE, LETTER> getNegKingdom(final CoRook<PLACE, LETTER> coRook) {
		return coRook.getCoKingdom().getNegKingdom().iterator().next();
	}

	/**
	 * Check if treaty(Rook) contains any non-maximal coset
	 *
	 * @param bp
	 *            Branching process of the refined Petri net
	 * @return True if the Rook contains a non cut.
	 */
	public boolean containsNonCut(final BranchingProcess<LETTER, PLACE> bp) {
		final Set<Set<Condition<LETTER, PLACE>>> census = getCensus();
		for (final Set<Condition<LETTER, PLACE>> coSet : census) {
			if (!isCut(coSet, bp)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Add a new town realm (only with specified condition) to Kingdom. And return a new Rook containing the kingdom.
	 *
	 * @param condition
	 *            Condition to create new realm with.
	 * @return Rook with modified Kingdom and the instances law.
	 */
	public Rook<PLACE, LETTER> expansion(final Condition<LETTER, PLACE> condition) {
		final Realm<PLACE, LETTER> realm = new Realm<>(ImmutableSet.of(Set.of(condition)));
		final Kingdom<PLACE, LETTER> newKingdom = mKingdom.addRealm(realm);
		return new Rook<>(newKingdom, getLaw());
	}

	/**
	 * Adds the condition to the specified existing realm of the rook's Kingdom and returns new Rook containing the
	 * changes in kingdom.
	 *
	 * @param coRook
	 *            coRook corresponding to Rook
	 * @return New Rook with condition added to specified realm. TODO: Kindred cases...
	 */
	public Rook<PLACE, LETTER> immigration(final CoRook<PLACE, LETTER> coRook) {
		final Condition<LETTER, PLACE> condition = coRook.getCondition();
		Realm<PLACE, LETTER> realm = getNegKingdom(coRook);
		Kingdom<PLACE, LETTER> kingdom = mKingdom.removeRealm(realm);
		realm = realm.addCondition(condition);
		kingdom = kingdom.addRealm(realm);
		return new Rook<>(kingdom, getLaw());
	}

	/**
	 * Adds new Realm containing condition and the conflict free conditions to Kingdom and removes the negative Kingdom
	 * from the set of Realms in Rook.
	 *
	 * @param coRook
	 *            coRook corresponding to Rook
	 * @return New Rook
	 */
	public Rook<PLACE, LETTER> foundation(final CoRook<PLACE, LETTER> coRook) {
		final Set<Realm<PLACE, LETTER>> newRealms =
				getKingdom().getRealms().stream().collect(Collectors.toCollection(HashSet::new));
		newRealms.remove(getNegKingdom(coRook));
		Set<Condition<LETTER, PLACE>> conflictFreeConditions = coRook.getCoKingdom().getConflictFreeConditions();
		conflictFreeConditions = DataStructureUtils.union(conflictFreeConditions, Set.of(coRook.getCondition()));
		final Realm<PLACE, LETTER> newRealm = new Realm<>(ImmutableSet.of(conflictFreeConditions));
		newRealms.add(newRealm);
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(ImmutableSet.of(newRealms));
		return new Rook<>(kingdom, getLaw());
	}

	public Rook<PLACE, LETTER> denial(final CoRook<PLACE, LETTER> coRook) {
		final Set<CoRealm<PLACE, LETTER>> partialCoRealms = coRook.getCoKingdom().getParCoRealms();
		assert partialCoRealms.size() == 1 : "There is more than one partial CoRealm discrimination case!";
		final CoRealm<PLACE, LETTER> partialCoRealm = partialCoRealms.iterator().next();
		Kingdom<PLACE, LETTER> kingdom = mKingdom.removeRealm(partialCoRealm.getRealm());
		final Set<Condition<LETTER, PLACE>> negativeConditions =
				DataStructureUtils.intersection(partialCoRealm.getConflictFreeSet(), partialCoRealm.getNegConditions());
		negativeConditions.add(coRook.getCondition());
		kingdom = kingdom.addRealm(new Realm<>(ImmutableSet.of(negativeConditions)));
		return new Rook<>(kingdom, getLaw());
	}

	/**
	 * Add condition to Rook's Law
	 *
	 * @param condition
	 *            Corresponding condition
	 * @return New Rook containing condition in its Law
	 */
	public Rook<PLACE, LETTER> approval(final Condition<LETTER, PLACE> condition) {
		final KingdomLaw<PLACE, LETTER> newLaw = mLaw.addCondition(condition);
		return new Rook<>(getKingdom(), newLaw);
	}

	/**
	 * Change Law of Rook to the Law only containing condition.
	 *
	 * @param coRook
	 *            CoRook corresponding to Rook
	 * @return New Rook with Law containing solely condition.
	 */
	public Rook<PLACE, LETTER> enactment(final CoRook<PLACE, LETTER> coRook) {
		final KingdomLaw<PLACE, LETTER> law = new KingdomLaw<>(ImmutableSet.of(Set.of(coRook.getCondition())));
		return new Rook<>(coRook.getRook().getKingdom(), law);
	}

	/**
	 * Create new Rook containing only the positive kingdom wrt. to coRook's condition.
	 *
	 * @param coRook
	 *            CoRook corresponding to Rook
	 * @return New Rook containing only the positive kingdom wrt. to coRook's condition
	 */
	public Rook<PLACE, LETTER> ratification(final CoRook<PLACE, LETTER> coRook) {
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(ImmutableSet.of(coRook.getCoKingdom().getPosKingdom()));
		final KingdomLaw<PLACE, LETTER> law = new KingdomLaw<>(ImmutableSet.of(Set.of(coRook.getCondition())));
		// final KingdomLaw<PLACE, LETTER> law = new KingdomLaw<>(
		// DataStructureUtils.union(coRook.getRook().getLaw().getConditions(), Set.of(coRook.getCondition())));
		return new Rook<>(kingdom, law);
	}

	/**
	 * Create new Rook containing in its kingdom all positive realms and a new realm containing only the positive
	 * corelated conditions of the old partial realm. The Law gets created by adding the coRook's condition to the old
	 * Law.
	 *
	 * @param coRook
	 *            CoRook corresponding to Rook
	 * @return New Rook as specified above
	 */
	public Rook<PLACE, LETTER> discrimination(final CoRook<PLACE, LETTER> coRook) {
		final Set<CoRealm<PLACE, LETTER>> partialCoRealms = coRook.getCoKingdom().getParCoRealms();
		assert partialCoRealms.size() == 1 : "There is more than one partial CoRealm discrimination case!";
		final CoRealm<PLACE, LETTER> partialCoRealm = partialCoRealms.iterator().next();
		Realm<PLACE, LETTER> partialRealm = partialCoRealm.getRealm();
		Kingdom<PLACE, LETTER> kingdom = mKingdom.removeRealm(partialRealm);
		partialRealm = partialRealm.removeCondition(partialCoRealm.getNegConditions());
		kingdom = kingdom.addRealm(partialRealm);
		final KingdomLaw<PLACE, LETTER> law = coRook.getRook().getLaw().addCondition(coRook.getCondition());
		return new Rook<>(kingdom, law);
	}

	public Set<Set<Condition<LETTER, PLACE>>> getCensus() {
		final Set<Set<Condition<LETTER, PLACE>>> treaty = mKingdom.getTreaty();
		final Set<Set<Condition<LETTER, PLACE>>> census = treaty.stream()
				.map(coset -> DataStructureUtils.union(coset, mLaw.getConditions())).collect(Collectors.toSet());
		return census;
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

	public static <P, L> boolean getRooksTerritoryEquality(final Set<Rook<P, L>> rooks) {
		final Set<Territory<P>> rookTerritories =
				rooks.stream().map(rook -> rook.getKingdom().toTerritory()).collect(Collectors.toSet());
		return (rookTerritories.size() == 1);
	}

	public static <P, L> boolean getRooksTerritoriesUnique(final Set<Rook<P, L>> rooks) {
		final Set<Territory<P>> rookTerritories =
				rooks.stream().map(rook -> rook.getKingdom().toTerritory()).collect(Collectors.toSet());
		return (rookTerritories.size() == rooks.size());
	}

	/**
	 * Get the cosets corresponding to marking in the Rook.
	 *
	 * @param subterr
	 *            A subterritory of a rook.
	 * @param marking
	 *            The marking we want to get all corresponding cosets of.
	 * @return All cosets in subterr which label to the marking.
	 */
	public Set<Set<Condition<LETTER, PLACE>>> getSubkingdom(final Set<SubterrElement<LETTER, PLACE>> subterr,
			final Marking<PLACE> marking) {
		final Set<Set<Condition<LETTER, PLACE>>> subkingdom = new HashSet<>();
		for (final SubterrElement<LETTER, PLACE> subterrElement : subterr) {
			if (subterrElement.getMarking().equals(marking)) {
				subkingdom.add(subterrElement.getCoSet());
			}
		}
		return subkingdom;
	}

	/**
	 * Get Places and corresponding Conditions of the Rook.
	 *
	 * @return HashRelation containing all (PLACE, Condition)-pairs of the Rook.
	 */
	public HashRelation<PLACE, Condition<LETTER, PLACE>> getPlacesToConditions() {
		final HashRelation<PLACE, Condition<LETTER, PLACE>> placesToConditions = new HashRelation<>();
		for (final Realm<PLACE, LETTER> realm : mKingdom.getRealms()) {
			for (final Condition<LETTER, PLACE> condition : realm.getConditions()) {
				placesToConditions.addPair(condition.getPlace(), condition);
			}
		}
		return placesToConditions;
	}

	/**
	 * Asserts that the Kingdom and Law of the Rook are valid. Further asserts that all conditions in the Law are
	 * positive co-related to the Kingdom. The function also asserts that all co-sets in census of the Rook are Cuts.
	 *
	 * @param bp
	 *            Branching of the refined Petri net.
	 * @param placesCoRelation
	 *            Contains the information about the corelation of the Places.
	 * @param assertConds
	 *            Assertion conditions of the refined Petri net.
	 */
	public boolean validityAssertion(final BranchingProcess<LETTER, PLACE> bp,
			final PlacesCoRelation<PLACE, LETTER> placesCoRelation) {

		if (!mKingdom.validityAssertion(placesCoRelation)) {
			assert false : "invalid kingdom";
			return false;
		}

		if (!mLaw.validityAssertion(bp)) {
			assert false : "invalid law";
			return false;
		}

		for (final Condition<LETTER, PLACE> assertionCondition : mLaw.getConditions()) {
			final CoKingdom<PLACE, LETTER> coKingdom =
					new CoKingdom<>(mKingdom, assertionCondition, bp, placesCoRelation);

			if (coKingdom.getCoRelation() != CoRelationType.POSITIVE) {
				assert false : "Not all assertion Conditions are positive co-related to the Kingdom";
				return false;
			}
		}

		if (containsNonCut(bp)) {
			assert false : "Not all co-sets in census of the Rook are Cuts";
			return false;
		}

		return true;
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
		final Rook<PLACE, LETTER> other = (Rook<PLACE, LETTER>) obj;
		return mKingdom.equals(other.getKingdom()) && mLaw.equals(other.getLaw());
	}

	@Override
	public int hashCode() {
		return Objects.hash(mKingdom, mLaw);
	}

	@Override
	public String toString() {
		return "Kingdom: " + mKingdom.toString() + " Law: " + mLaw.toString();
	}
}
