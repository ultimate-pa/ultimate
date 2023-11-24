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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
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
public final class CrownConstruction<PLACE, LETTER> {

	private final BranchingProcess<LETTER, PLACE> mBp;

	private final Crown<PLACE, LETTER> mCrown;

	private final Crown<PLACE, LETTER> mPreCrown;

	private final Set<Condition<LETTER, PLACE>> mOrigConds;

	private final Set<Condition<LETTER, PLACE>> mAssertConds;

	private final PlacesCoRelation<PLACE, LETTER> mPlacesCoRelation;

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
			final Set<Condition<LETTER, PLACE>> originalConditionSet = new HashSet<>(Set.of(originalCondition));
			final Realm<PLACE, LETTER> realm = new Realm<>(originalConditionSet);
			final Set<Realm<PLACE, LETTER>> realmSet = new HashSet<>(Set.of(realm));
			final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(realmSet);
			for (final Condition<LETTER, PLACE> assertionCondition : mAssertConds) {
				final CoKingdom<PLACE, LETTER> coKingdom =
						new CoKingdom<>(kingdom, assertionCondition, mBp, mPlacesCoRelation);
				if (coKingdom.getCoRelation() == CoRelationType.POSITIVE) {
					final Set<Condition<LETTER, PLACE>> lawConditions = new HashSet<>(Set.of(assertionCondition));
					final KingdomLaw<PLACE, LETTER> kingdomLaw = new KingdomLaw<>(lawConditions);
					final Rook<PLACE, LETTER> rook = new Rook<>(kingdom, kingdomLaw);
					mPreCrown.addRook(rook);
				}
			}
		}
	}

	private Set<Rook<PLACE, LETTER>> crownComputation() {
		Set<Rook<PLACE, LETTER>> colonizedRooks = mPreCrown.getRooks();
		for (final Rook<PLACE, LETTER> rook : new HashSet<>(colonizedRooks)) {
			colonizedRooks = crownExpansion(rook, new ArrayList<>(mOrigConds), colonizedRooks, true);
		}
		Set<Rook<PLACE, LETTER>> colonizedpreRooks = computePreRooks(colonizedRooks);
		colonizedRooks = DataStructureUtils.difference(colonizedRooks, colonizedpreRooks);
		for (final Rook<PLACE, LETTER> rook : new HashSet<>(colonizedRooks)) {
			colonizedRooks = crownExpansion(rook, new ArrayList<>(mAssertConds), colonizedRooks, false);
		}
		colonizedpreRooks = computePreRooks(colonizedRooks);
		colonizedRooks = DataStructureUtils.difference(colonizedRooks, colonizedpreRooks);
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
				if (!getRooksTerritoryEquality(kindredRooks)) {
					splitMarkings.add(marking);
				}
			}
			final Set<Condition<LETTER, PLACE>> allKindredConditions =
					kindred.getKindredConditions(splitMarkings, rook);
			final Set<Realm<PLACE, LETTER>> kindredRealms = kindred.getKindredRealms(allKindredConditions, rook);
			final Kingdom<PLACE, LETTER> firstKingdom =
					new Kingdom<>(DataStructureUtils.difference(rook.getKingdom().getRealms(), kindredRealms));
			for (final Realm<PLACE, LETTER> realm : kindredRealms) {
				final Set<Condition<LETTER, PLACE>> newRealmConditions =
						DataStructureUtils.difference(realm.getConditions(), allKindredConditions);
				firstKingdom.addRealm(new Realm<>(newRealmConditions));
			}
			mCrown.removeRook(rook);
			mCrown.addRook(new Rook<>(firstKingdom, rook.getLaw()));
			for (final Marking<PLACE> marking : splitMarkings) {
				final Set<Condition<LETTER, PLACE>> markingKindredConds = kindred.getKindredConditions(marking, rook);
				final Kingdom<PLACE, LETTER> secondKingdom =
						new Kingdom<>(DataStructureUtils.difference(rook.getKingdom().getRealms(), kindredRealms));
				for (final Condition<LETTER, PLACE> condition : markingKindredConds) {
					secondKingdom.addRealm(new Realm<>(new HashSet<>(Set.of(condition))));
				}
				mCrown.addRook(new Rook<>(secondKingdom, rook.getLaw()));
			}
		}
	}

	private Set<Rook<PLACE, LETTER>> crownExpansion(final Rook<PLACE, LETTER> rook,
			final List<Condition<LETTER, PLACE>> troopConditions, Set<Rook<PLACE, LETTER>> crownRooks,
			final boolean colonizer) {
		for (final Condition<LETTER, PLACE> condition : troopConditions) {
			final List<Condition<LETTER, PLACE>> conditions = new ArrayList<>(troopConditions);
			Rook<PLACE, LETTER> colonyRook;
			if (colonizer) {
				colonyRook = colonize(condition, rook);
			} else {
				colonyRook = legislate(condition, rook);
			}
			if (colonyRook == null) {
				conditions.remove(condition);
			} else {
				final List<Condition<LETTER, PLACE>> ntroops =
						conditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
				Set<Rook<PLACE, LETTER>> expandedRooks = crownExpansion(colonyRook, ntroops, crownRooks, colonizer);
				expandedRooks.add(colonyRook);
				final Set<Rook<PLACE, LETTER>> preRooks = computePreRooks(expandedRooks);
				expandedRooks = DataStructureUtils.difference(expandedRooks, preRooks);
				crownRooks = DataStructureUtils.union(crownRooks, expandedRooks);
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
			colonyRook = expand(coRook);
			break;
		case IMMIGRATION:
			colonyRook = immigrate(coRook);
			break;
		case FOUNDATION:
			colonyRook = founding(coRook);
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
			colonyRook = approve(coRook);
			break;
		case ENACTMENT:
			colonyRook = enactment(coRook);
			break;
		case RATIFICATION:
			colonyRook = ratify(coRook);
			break;
		default:
			colonyRook = null;
		}
		return colonyRook;
	}

	private boolean isColonizer(final Condition<LETTER, PLACE> condition) {
		return mOrigConds.contains(condition);
	}

	private Rook<PLACE, LETTER> expand(final CoRook<PLACE, LETTER> coRook) {
		Rook<PLACE, LETTER> rook = coRook.getRook();
		rook = rook.expansion(coRook.getCondition());
		return rook;
	}

	private Rook<PLACE, LETTER> immigrate(final CoRook<PLACE, LETTER> coRook) {
		Rook<PLACE, LETTER> rook = coRook.getRook();
		rook = rook.immigration(coRook.getCondition(), getNegKingdom(coRook));
		return rook;
	}

	private Rook<PLACE, LETTER> founding(final CoRook<PLACE, LETTER> coRook) {
		final Rook<PLACE, LETTER> rook = coRook.getRook();
		final Set<Realm<PLACE, LETTER>> newRealms = rook.getKingdom().getRealms();
		newRealms.remove(getNegKingdom(coRook));
		final Set<Condition<LETTER, PLACE>> conflictFreeConditions = coRook.getCoKingdom().getConflictFreeConditions();
		conflictFreeConditions.add(coRook.getCondition());
		final Realm<PLACE, LETTER> newRealm = new Realm<>(conflictFreeConditions);
		newRealms.add(newRealm);
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(newRealms);
		return new Rook<>(kingdom, rook.getLaw());
	}

	private Rook<PLACE, LETTER> approve(final CoRook<PLACE, LETTER> coRook) {
		Rook<PLACE, LETTER> rook = coRook.getRook();
		rook = rook.approval(coRook.getCondition());
		return rook;
	}

	private Rook<PLACE, LETTER> ratify(final CoRook<PLACE, LETTER> coRook) {
		final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(coRook.getCoKingdom().getPosKingdom());
		final KingdomLaw<PLACE, LETTER> law =
				new KingdomLaw<>(new HashSet<Condition<LETTER, PLACE>>(Set.of(coRook.getCondition())));
		return new Rook<>(kingdom, law);
	}

	private Rook<PLACE, LETTER> enactment(final CoRook<PLACE, LETTER> coRook) {
		final KingdomLaw<PLACE, LETTER> law =
				new KingdomLaw<>(new HashSet<Condition<LETTER, PLACE>>(Set.of(coRook.getCondition())));
		return new Rook<>(coRook.getRook().getKingdom(), law);
	}

	private Realm<PLACE, LETTER> getNegKingdom(final CoRook<PLACE, LETTER> coRook) {
		return coRook.getCoKingdom().getNegKingdom().iterator().next();
	}

	private Set<Rook<PLACE, LETTER>> computePreRooks(final Set<Rook<PLACE, LETTER>> rooks) {
		final Set<Rook<PLACE, LETTER>> preRooks =
				rooks.stream().filter(rook -> rook.containsNonCut(mBp)).collect(Collectors.toSet());
		return preRooks;
	}

	private boolean getRooksTerritoryEquality(final Set<Rook<PLACE, LETTER>> rooks) {
		final Set<Territory<PLACE, LETTER>> rookTerritories =
				rooks.stream().map(rook -> new Territory<PLACE, LETTER>(rook.getKingdom())).collect(Collectors.toSet());
		return (rookTerritories.size() == 1);
	}

	public Crown<PLACE, LETTER> getCrown() {
		return mCrown;
	}

}
