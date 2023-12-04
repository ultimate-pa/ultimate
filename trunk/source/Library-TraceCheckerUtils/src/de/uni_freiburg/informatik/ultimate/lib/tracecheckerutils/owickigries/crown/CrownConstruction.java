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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class CrownConstruction<PLACE, LETTER> {

	private final BranchingProcess<LETTER, PLACE> mBp;

	private final Crown<PLACE, LETTER> mCrown;

	private final Crown<PLACE, LETTER> mPreCrown;

	private final Set<Condition<LETTER, PLACE>> mOrigConds;

	private final Set<Condition<LETTER, PLACE>> mAssertConds;

	private final PlacesCoRelation<PLACE, LETTER> mPlacesCoRelation;

	// Store already determined information about a rook containing non cuts to save runtime
	private final HashMap<Rook<PLACE, LETTER>, Boolean> mContainsNonCut = new HashMap<>();

	public CrownConstruction(final BranchingProcess<LETTER, PLACE> bp, final Set<Condition<LETTER, PLACE>> origConds,
			final Set<Condition<LETTER, PLACE>> assertConds, final IPetriNet<LETTER, PLACE> net) {
		mBp = bp;
		mCrown = new Crown<>(mBp);
		mPreCrown = new Crown<>(mBp);
		mOrigConds = origConds;
		mAssertConds = assertConds;
		mPlacesCoRelation = new PlacesCoRelation<>(bp);
		settlements();
		mCrown.addRook(crownComputation());
		crownRefurbishment();
		mCrown.validityAssertion(mPlacesCoRelation, assertConds);
	}

	private void settlements() {
		// Create a new rook for each original condition.
		// Add a to crown a new rook with "capital" and one corelated assertion condition
		for (final Condition<LETTER, PLACE> originalCondition : mOrigConds) {
			final Set<Condition<LETTER, PLACE>> originalConditionSet = Set.of(originalCondition);
			final Realm<PLACE, LETTER> realm = new Realm<>(ImmutableSet.of(originalConditionSet));
			final Set<Realm<PLACE, LETTER>> realmSet = Set.of(realm);
			final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(ImmutableSet.of(realmSet));
			for (final Condition<LETTER, PLACE> assertionCondition : mAssertConds) {
				final CoKingdom<PLACE, LETTER> coKingdom =
						new CoKingdom<>(kingdom, assertionCondition, mBp, mPlacesCoRelation);
				if (coKingdom.getCoRelation() == CoRelationType.POSITIVE) {
					final Set<Condition<LETTER, PLACE>> lawConditions = Set.of(assertionCondition);
					final KingdomLaw<PLACE, LETTER> kingdomLaw = new KingdomLaw<>(ImmutableSet.of(lawConditions));
					final Rook<PLACE, LETTER> rook = new Rook<>(kingdom, kingdomLaw);
					mPreCrown.addRook(rook);
				}
			}
		}
	}

	private Set<Rook<PLACE, LETTER>> crownComputation() {
		final Set<Rook<PLACE, LETTER>> colonizedRooks = mPreCrown.getRooks();
		final Set<Rook<PLACE, LETTER>> reSet = new HashSet<>();
		for (final Rook<PLACE, LETTER> rook : colonizedRooks) {
			reSet.addAll(crownExpansionRecursive(rook, new ArrayList<>(mOrigConds), true));
		}
		colonizedRooks.clear();
		for (final Rook<PLACE, LETTER> rook : reSet) {
			colonizedRooks.addAll(crownExpansionRecursive(rook, new ArrayList<>(mAssertConds), false));
		}
		// final Set<Rook<PLACE, LETTER>> colonizedpreRooks = computePreRooks(colonizedRooks);
		// colonizedRooks.removeAll(colonizedpreRooks);
		return colonizedRooks;
	}

	private void crownRefurbishment() {
		final Kindred<PLACE, LETTER> kindred = new Kindred<>(mCrown);
		final List<Rook<PLACE, LETTER>> crownRooks = new ArrayList<>(mCrown.getRooks());
		for (final Rook<PLACE, LETTER> rook : crownRooks) {
			final Set<Marking<PLACE>> kindredMarkings = kindred.getKindredMarkings(rook);
			if (kindredMarkings.isEmpty()) {
				continue;
			}
			final Set<Marking<PLACE>> splitMarkings = new HashSet<>();
			for (final Marking<PLACE> marking : kindredMarkings) {
				final Set<Rook<PLACE, LETTER>> kindredRooks = kindred.getKindredRooks(marking);
				if (!Territory.getRooksTerritoryEquality(kindredRooks)) {
					splitMarkings.add(marking);
				}
			}
			final Set<Condition<LETTER, PLACE>> allKindredConditions =
					kindred.getKindredConditions(splitMarkings, rook);
			final Set<Realm<PLACE, LETTER>> kindredRealms = kindred.getKindredRealms(allKindredConditions, rook);
			Kingdom<PLACE, LETTER> firstKingdom = new Kingdom<>(
					ImmutableSet.of(DataStructureUtils.difference(rook.getKingdom().getRealms(), kindredRealms)));
			for (final Realm<PLACE, LETTER> realm : kindredRealms) {
				final ImmutableSet<Condition<LETTER, PLACE>> newRealmConditions =
						ImmutableSet.of(DataStructureUtils.difference(realm.getConditions(), allKindredConditions));
				firstKingdom = firstKingdom.addRealm(new Realm<>(newRealmConditions));
			}
			mCrown.removeRook(rook);
			mCrown.addRook(new Rook<>(firstKingdom, rook.getLaw()));
			for (final Marking<PLACE> marking : splitMarkings) {
				final Set<Condition<LETTER, PLACE>> markingKindredConds = kindred.getKindredConditions(marking, rook);
				Kingdom<PLACE, LETTER> secondKingdom = new Kingdom<>(
						ImmutableSet.of(DataStructureUtils.difference(rook.getKingdom().getRealms(), kindredRealms)));
				for (final Condition<LETTER, PLACE> condition : markingKindredConds) {
					secondKingdom = secondKingdom.addRealm(new Realm<>(ImmutableSet.of(Set.of(condition))));
				}
				mCrown.addRook(new Rook<>(secondKingdom, rook.getLaw()));
			}
		}
	}

	// Recursive expansion
	private Set<Rook<PLACE, LETTER>> crownExpansionRecursive(final Rook<PLACE, LETTER> rook,
			final List<Condition<LETTER, PLACE>> troopConditions, final boolean colonizer) {
		final Set<Rook<PLACE, LETTER>> crownRooks = new HashSet<>();
		boolean isMaximal = true;
		final List<Condition<LETTER, PLACE>> conditions = new ArrayList<>(troopConditions);
		for (int i = 0; i < troopConditions.size(); i++) {
			final Condition<LETTER, PLACE> condition = troopConditions.get(i);
			Rook<PLACE, LETTER> colonyRook;
			if (colonizer) {
				colonyRook = colonize(condition, rook);
			} else {
				colonyRook = legislate(condition, rook);
			}
			if (colonyRook == null) {
				conditions.remove(condition);
			} else {
				isMaximal = false;
				final List<Condition<LETTER, PLACE>> ntroops =
						conditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
				final Set<Rook<PLACE, LETTER>> expandedRooks = crownExpansionRecursive(colonyRook, ntroops, colonizer);
				crownRooks.addAll(expandedRooks);
			}
		}
		if (isMaximal) {
			crownRooks.add(rook);
		}
		return crownRooks;
	}

	// Iterative expansion using two stacks
	private Set<Rook<PLACE, LETTER>> crownExpansionIterative(final Rook<PLACE, LETTER> rook,
			final List<Condition<LETTER, PLACE>> troopConditions, final boolean colonizer) {
		final Set<Rook<PLACE, LETTER>> crownRooks = new HashSet<>();
		final Deque<Rook<PLACE, LETTER>> rookStack = new LinkedList<>();
		final Deque<List<Condition<LETTER, PLACE>>> conditionStack = new LinkedList<>();
		rookStack.push(rook);
		conditionStack.push(troopConditions);
		boolean isMaximal = true;
		while (!(rookStack.isEmpty() || conditionStack.isEmpty())) {
			final Rook<PLACE, LETTER> currentRook = rookStack.pop();
			final List<Condition<LETTER, PLACE>> currentConditions = conditionStack.pop();
			isMaximal = true;
			final List<Condition<LETTER, PLACE>> conditions = new ArrayList<>(currentConditions);
			for (int i = 0; i < currentConditions.size(); i++) {
				final Condition<LETTER, PLACE> condition = currentConditions.get(i);
				Rook<PLACE, LETTER> colonyRook;
				if (colonizer) {
					colonyRook = colonize(condition, currentRook);
				} else {
					colonyRook = legislate(condition, currentRook);
				}
				if (colonyRook == null) {
					conditions.remove(condition);
				} else {
					isMaximal = false;
					final List<Condition<LETTER, PLACE>> ntroops =
							conditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
					rookStack.push(colonyRook);
					conditionStack.push(ntroops);
				}
			}
			if (isMaximal) {
				crownRooks.add(currentRook);
			}
		}

		return crownRooks;
	}

	private Rook<PLACE, LETTER> colonize(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook) {
		final boolean colonizer = isColonizer(condition);
		final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer, mPlacesCoRelation);
		Rook<PLACE, LETTER> colonyRook;
		switch (coRook.getColonization()) {
		case EXPANSION:
			colonyRook = rook.expansion(condition);
			break;
		case IMMIGRATION:
			colonyRook = rook.immigration(coRook);
			break;
		case FOUNDATION:
			colonyRook = rook.foundation(coRook);
			break;
		default:
			colonyRook = null;
		}
		return colonyRook;
	}

	private Rook<PLACE, LETTER> legislate(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook) {
		final boolean colonizer = isColonizer(condition);
		final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer, mPlacesCoRelation);
		Rook<PLACE, LETTER> colonyRook;
		switch (coRook.getLegislation()) {
		case APPROVAL:
			colonyRook = rook.approval(condition);
			break;
		case ENACTMENT:
			colonyRook = rook.enactment(coRook);
			break;
		case RATIFICATION:
			colonyRook = rook.ratification(coRook);
			break;
		default:
			colonyRook = null;
		}
		return colonyRook;
	}

	private boolean isColonizer(final Condition<LETTER, PLACE> condition) {
		return mOrigConds.contains(condition);
	}

	private Set<Rook<PLACE, LETTER>> computePreRooks(final Set<Rook<PLACE, LETTER>> rooks) {
		final Set<Rook<PLACE, LETTER>> preRooks =
				rooks.stream().filter(rook -> containsNonCut(rook)).collect(Collectors.toSet());
		return preRooks;
	}

	private boolean containsNonCut(final Rook<PLACE, LETTER> rook) {
		final Boolean noCut = mContainsNonCut.computeIfAbsent(rook, r -> r.containsNonCut(mBp));
		return noCut;
	}

	public Crown<PLACE, LETTER> getCrown() {
		return mCrown;
	}

}
