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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.MinMaxMed;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public final class CrownConstruction<PLACE, LETTER> {
	public static final boolean SINGLE_ASSERTION_LAWS = false;

	private final ILogger mLogger;

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final Set<Condition<LETTER, PLACE>> mOrigConds;
	private final Set<Condition<LETTER, PLACE>> mAssertConds;

	private final PlacesCoRelation<PLACE> mPlacesCoRelation;

	private final Crown<PLACE, LETTER> mCrown;

	private final Statistics mStatistics = new Statistics();

	private final Set<Pair<Condition<LETTER, PLACE>, Rook<PLACE, LETTER>>> mRejectedPairs = new HashSet<>();

	public CrownConstruction(final IUltimateServiceProvider services, final BranchingProcess<LETTER, PLACE> bp,
			final Set<Condition<LETTER, PLACE>> origConds, final Set<Condition<LETTER, PLACE>> assertConds) {
		mLogger = services.getLoggingService().getLogger(CrownConstruction.class);
		mLogger.setLevel(LogLevel.INFO);

		mBp = bp;
		mOrigConds = origConds;
		mAssertConds = assertConds;
		mPlacesCoRelation = new PlacesCoRelation<>(bp);
		final Set<Condition<LETTER, PLACE>> singletonConditions = getSingletonConditions();
		final Set<Condition<LETTER, PLACE>> expansionConditions =
				DataStructureUtils.difference(mOrigConds, singletonConditions);
		Set<Rook<PLACE, LETTER>> singletonRooks = buildSingletonRooks(singletonConditions);
		singletonRooks = combineSingletonRooks(singletonRooks);

		final var settlementRooks = mStatistics.measureSettlement(() -> settlements(expansionConditions));
		final var crownRooks =
				mStatistics.measureCrownComputation(() -> crownComputation(settlementRooks, expansionConditions));
		mLogger.debug("Crown before refurbishment:\n%s\n", new Crown<>(bp, crownRooks));
		crownRooks.addAll(singletonRooks);
		final var refurbishedRooks = mStatistics.measureRefurbishment(() -> crownRefurbishment(crownRooks));
		mCrown = new Crown<>(bp, refurbishedRooks);
		mStatistics.reportCrown(mCrown);

		assert mCrown.validityAssertion(mPlacesCoRelation);
	}

	private Set<Condition<LETTER, PLACE>> getSingletonConditions() {
		final Set<Condition<LETTER, PLACE>> singletonConditions = new HashSet<>();
		final ICoRelation<LETTER, PLACE> coRelation = mBp.getCoRelation();
		for (final Condition<LETTER, PLACE> condition : mOrigConds) {
			final Set<Condition<LETTER, PLACE>> corelatedConditions =
					coRelation.computeCoRelatatedConditions(condition);
			corelatedConditions.removeAll(mAssertConds);
			corelatedConditions.remove(condition);
			if (corelatedConditions.isEmpty()) {
				singletonConditions.add(condition);
			}
		}
		return singletonConditions;
	}

	private Set<Rook<PLACE, LETTER>> buildSingletonRooks(final Set<Condition<LETTER, PLACE>> singletonConditions) {
		final Set<Rook<PLACE, LETTER>> singletonRooks = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : singletonConditions) {
			final Realm<PLACE, LETTER> singletonRealm = new Realm<>(ImmutableSet.singleton(condition));
			final Rook<PLACE, LETTER> singletonRook = new Rook<>(new Kingdom<>(ImmutableSet.singleton(singletonRealm)),
					new KingdomLaw<>(ImmutableSet.empty()));
			singletonRooks.add(singletonRook);
		}
		return crownExpansionIterative2(singletonRooks, new ArrayList<>(mAssertConds), false);
	}

	private Set<Rook<PLACE, LETTER>> combineSingletonRooks(final Set<Rook<PLACE, LETTER>> singletonRooks) {
		final HashRelation<KingdomLaw<PLACE, LETTER>, Kingdom<PLACE, LETTER>> lawKingdomRelation = new HashRelation<>();
		for (final Rook<PLACE, LETTER> rook : singletonRooks) {
			lawKingdomRelation.addPair(rook.getLaw(), rook.getKingdom());
		}
		final Set<Rook<PLACE, LETTER>> combinedRooks = new HashSet<>();
		for (final KingdomLaw<PLACE, LETTER> law : lawKingdomRelation.getDomain()) {
			final Set<Kingdom<PLACE, LETTER>> kingdoms = lawKingdomRelation.getImage(law);
			final Rook<PLACE, LETTER> combinedRook = new Rook<>(combineSingletonKingdoms(kingdoms), law);
			combinedRooks.add(combinedRook);
		}
		return combinedRooks;
	}

	private Kingdom<PLACE, LETTER> combineSingletonKingdoms(final Set<Kingdom<PLACE, LETTER>> singletonKingdoms) {
		final Set<Condition<LETTER, PLACE>> combinedConditions = new HashSet<>();
		for (final Kingdom<PLACE, LETTER> kingdom : singletonKingdoms) {
			assert kingdom.getRealms().size() == 1 : "Kingdom is not a singleton Kingdom";
			for (final Realm<PLACE, LETTER> realm : kingdom.getRealms()) {
				assert realm.getConditions().size() == 1 : "Realm is not a singleton Realm";
				combinedConditions.addAll(realm.getConditions());
			}
		}
		final Realm<PLACE, LETTER> combinedRealm = new Realm<>(ImmutableSet.of(combinedConditions));
		return new Kingdom<>(ImmutableSet.singleton(combinedRealm));
	}

	private Set<Rook<PLACE, LETTER>> settlements(final Set<Condition<LETTER, PLACE>> conditions) {
		// Create a new rook for each original condition.
		// Add a to crown a new rook with "capital" and one corelated assertion condition
		final Set<Rook<PLACE, LETTER>> settlementRooks = new HashSet<>();
		for (final Condition<LETTER, PLACE> originalCondition : conditions) {
			final Realm<PLACE, LETTER> realm = new Realm<>(ImmutableSet.singleton(originalCondition));
			final Kingdom<PLACE, LETTER> kingdom = new Kingdom<>(ImmutableSet.singleton(realm));
			for (final Condition<LETTER, PLACE> assertionCondition : mAssertConds) {
				final CoKingdom<PLACE, LETTER> coKingdom =
						new CoKingdom<>(kingdom, assertionCondition, mBp, mPlacesCoRelation);
				if (coKingdom.getCoRelation() == CoRelationType.POSITIVE) {
					final KingdomLaw<PLACE, LETTER> kingdomLaw =
							new KingdomLaw<>(ImmutableSet.singleton(assertionCondition));
					final Rook<PLACE, LETTER> rook = new Rook<>(kingdom, kingdomLaw);
					settlementRooks.add(rook);
				}
			}
		}
		return settlementRooks;
	}

	private Set<Rook<PLACE, LETTER>> crownComputation(final Set<Rook<PLACE, LETTER>> colonizedRooks,
			final Set<Condition<LETTER, PLACE>> expansionConditions) {
		mLogger.debug("Starting Crown Computation...");
		mLogger.debug("Starting Colonization...");
		final Set<Rook<PLACE, LETTER>> reSet =
				crownExpansionIterative2(colonizedRooks, new ArrayList<>(expansionConditions), true);
		mRejectedPairs.clear();
		if (SINGLE_ASSERTION_LAWS) {
			reSet.removeIf(r -> r.containsNonCut(mBp, mOrigConds));
			return reSet;
		}
		mLogger.debug("Starting Legislation...");
		final Set<Rook<PLACE, LETTER>> legislationRooks =
				crownExpansionIterative2(reSet, new ArrayList<>(mAssertConds), false);

		// remove pre-rooks
		legislationRooks.removeIf(r -> r.containsNonCut(mBp, mBp.getConditions()));

		return legislationRooks;
	}

	// Recursive expansion
	private Set<Rook<PLACE, LETTER>> crownExpansionRecursive(final Rook<PLACE, LETTER> rook,
			final List<Condition<LETTER, PLACE>> troopConditions, final boolean colonizer) {
		final Set<Rook<PLACE, LETTER>> crownRooks = new HashSet<>();
		boolean isMaximal = true;
		for (final Condition<LETTER, PLACE> condition : troopConditions) {
			assert !PetriOwickiGries.IGNORE_CUTOFF_CONDITIONS
					|| !PetriOwickiGries.isCutoff(condition) : "unexpected cutoff condition";
			final Pair<Condition<LETTER, PLACE>, Rook<PLACE, LETTER>> pair = new Pair<>(condition, rook);
			if (mRejectedPairs.contains(pair)) {
				continue;
			}
			Rook<PLACE, LETTER> colonyRook;
			if (colonizer) {
				final Pair<Rook<PLACE, LETTER>, Boolean> colonyPair = colonize(condition, rook);
				colonyRook = colonyPair.getFirst();
			} else {
				colonyRook = legislate(condition, rook);
			}
			if (colonyRook == null) {
				mRejectedPairs.add(pair);
				continue;
			}
			isMaximal = false;
			final List<Condition<LETTER, PLACE>> ntroops =
					troopConditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
			final Set<Rook<PLACE, LETTER>> expandedRooks = crownExpansionRecursive(colonyRook, ntroops, colonizer);
			crownRooks.addAll(expandedRooks);
		}
		if (isMaximal) {
			crownRooks.add(rook);
		}
		return crownRooks;
	}

	private Set<Rook<PLACE, LETTER>> crownExpansionIterative(final Rook<PLACE, LETTER> rook,
			final List<Condition<LETTER, PLACE>> troopConditions, final boolean colonizer) {
		final Set<Rook<PLACE, LETTER>> crownRooks = new HashSet<>();
		final HashDeque<Pair<Rook<PLACE, LETTER>, List<Condition<LETTER, PLACE>>>> rookStack = new HashDeque<>();
		rookStack.offer(new Pair<>(rook, troopConditions));
		boolean isMaximal = true;
		while (!(rookStack.isEmpty())) {
			final Pair<Rook<PLACE, LETTER>, List<Condition<LETTER, PLACE>>> currentPair = rookStack.poll();
			final Rook<PLACE, LETTER> currentRook = currentPair.getFirst();
			final List<Condition<LETTER, PLACE>> currentConditions = currentPair.getSecond();
			isMaximal = true;
			for (int i = 0; i < currentConditions.size(); i++) {
				final Condition<LETTER, PLACE> condition = currentConditions.get(i);
				final Pair<Condition<LETTER, PLACE>, Rook<PLACE, LETTER>> pair = new Pair<>(condition, currentRook);
				if (mRejectedPairs.contains(pair)) {
					continue;
				}
				Rook<PLACE, LETTER> colonyRook;
				if (colonizer) {
					colonyRook = colonize(condition, currentRook).getFirst();
				} else {
					colonyRook = legislate(condition, currentRook);
				}
				if (colonyRook == null) {
					mRejectedPairs.add(pair);
					continue;
				}
				isMaximal = false;
				final List<Condition<LETTER, PLACE>> ntroops =
						currentConditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
				rookStack.offer(new Pair<>(colonyRook, ntroops));
			}

			if (isMaximal) {
				crownRooks.add(currentRook);
			}
			if (rookStack.isEmpty()) {
				break;
			}
		}

		return crownRooks;
	}

	// Iterative expansion using BFS
	private Set<Rook<PLACE, LETTER>> crownExpansionIterative2(final Set<Rook<PLACE, LETTER>> rooks,
			final List<Condition<LETTER, PLACE>> troopConditions, final boolean colonizer) {
		final Set<Rook<PLACE, LETTER>> crownRooks = new HashSet<>();
		final HashDeque<Rook<PLACE, LETTER>> rookQueue = new HashDeque<>();
		final Map<Rook<PLACE, LETTER>, List<Condition<LETTER, PLACE>>> rookConditionMap = new HashMap<>();
		final Set<Rook<PLACE, LETTER>> seenRooks = new HashSet<>();
		for (final Rook<PLACE, LETTER> rook : rooks) {
			rookQueue.offer(rook);
			rookConditionMap.put(rook, troopConditions);
		}
		boolean isMaximal = true;
		while (!(rookQueue.isEmpty())) {
			final Rook<PLACE, LETTER> currentRook = rookQueue.poll();
			if (!seenRooks.add(currentRook)) {
				continue;
			}
			final List<Condition<LETTER, PLACE>> currentConditions =
					rookConditionMap.computeIfAbsent(currentRook, r -> troopConditions);
			isMaximal = true;
			final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>(currentConditions);
			for (int i = 0; i < currentConditions.size(); i++) {
				final Condition<LETTER, PLACE> condition = currentConditions.get(i);
				final Pair<Condition<LETTER, PLACE>, Rook<PLACE, LETTER>> pair = new Pair<>(condition, currentRook);
				if (mRejectedPairs.contains(pair)) {
					continue;
				}
				Rook<PLACE, LETTER> colonyRook;
				boolean useAllConds;
				if (colonizer) {
					final Pair<Rook<PLACE, LETTER>, Boolean> colonyPair = colonize(condition, currentRook);
					colonyRook = colonyPair.getFirst();
					useAllConds = colonyPair.getSecond().booleanValue();
				} else {
					colonyRook = legislate(condition, currentRook);
					useAllConds = false;
				}
				if (colonyRook == null) {
					conditions.remove(condition);
					mRejectedPairs.add(pair);
					continue;
				}
				isMaximal = false;
				final List<Condition<LETTER, PLACE>> ntroops;
				if (useAllConds) {
					ntroops = currentConditions.stream().filter(cond -> !cond.equals(condition))
							.collect(Collectors.toList());
				} else {
					ntroops = conditions.stream().filter(cond -> !cond.equals(condition)).collect(Collectors.toList());
				}
				rookQueue.offer(colonyRook);
				rookConditionMap.put(colonyRook, ntroops);
			}

			if (isMaximal) {
				crownRooks.add(currentRook);
			}
		}

		return crownRooks;
	}

	private Set<Rook<PLACE, LETTER>> crownRefurbishment(final Set<Rook<PLACE, LETTER>> rooks) {
		final Kindred<PLACE, LETTER> kindred = new Kindred<>(rooks);
		final List<Rook<PLACE, LETTER>> crownRooks = new ArrayList<>(rooks);
		for (final Rook<PLACE, LETTER> rook : crownRooks) {
			final Set<Marking<PLACE>> kindredMarkings = kindred.getKindredMarkings(rook);
			if (kindredMarkings.isEmpty()) {
				continue;
			}
			final Set<Marking<PLACE>> splitMarkings = new HashSet<>();
			for (final Marking<PLACE> marking : kindredMarkings) {
				final Set<Rook<PLACE, LETTER>> kindredRooks = kindred.getKindredRooks(marking);
				if (!Rook.getRooksTerritoryEquality(kindredRooks)) {
					splitMarkings.add(marking);
				}
			}
			final Set<Condition<LETTER, PLACE>> allKindredConditions =
					kindred.getKindredConditions(splitMarkings, rook);
			final Set<Realm<PLACE, LETTER>> kindredRealms = kindred.getKindredRealms(allKindredConditions, rook);
			Kingdom<PLACE, LETTER> firstKingdom = new Kingdom<>(
					ImmutableSet.of(DataStructureUtils.difference(rook.getKingdom().getRealms(), kindredRealms)));
			final Set<Realm<PLACE, LETTER>> nonKindredRealms = new HashSet<>();
			boolean addRook = true;
			for (final Realm<PLACE, LETTER> realm : kindredRealms) {
				final ImmutableSet<Condition<LETTER, PLACE>> newRealmConditions =
						ImmutableSet.of(DataStructureUtils.difference(realm.getConditions(), allKindredConditions));
				if (newRealmConditions.isEmpty()) {
					addRook = false;
					break;
				}
				nonKindredRealms.add(new Realm<>(newRealmConditions));
			}
			if (!addRook) {
				continue;
			}
			rooks.remove(rook);
			firstKingdom = firstKingdom.addRealm(nonKindredRealms);
			rooks.add(new Rook<>(firstKingdom, rook.getLaw()));
			for (final Marking<PLACE> marking : splitMarkings) {
				final Set<Condition<LETTER, PLACE>> markingKindredConds = kindred.getKindredConditions(marking, rook);
				final Set<Realm<PLACE, LETTER>> markingKindredRealms =
						kindred.getKindredRealms(markingKindredConds, rook);
				Kingdom<PLACE, LETTER> secondKingdom = new Kingdom<>(ImmutableSet
						.of(DataStructureUtils.difference(rook.getKingdom().getRealms(), markingKindredRealms)));
				for (final Condition<LETTER, PLACE> condition : markingKindredConds) {
					secondKingdom = secondKingdom.addRealm(new Realm<>(ImmutableSet.singleton(condition)));
				}
				rooks.add(new Rook<>(secondKingdom, rook.getLaw()));
			}
		}
		return rooks;
	}

	private Pair<Rook<PLACE, LETTER>, Boolean> colonize(final Condition<LETTER, PLACE> condition,
			final Rook<PLACE, LETTER> rook) {
		final boolean colonizer = isColonizer(condition);
		final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer, mPlacesCoRelation);
		Rook<PLACE, LETTER> colonyRook;
		Boolean useAllConds = false;
		final ColonizationType colonizationType = coRook.getColonization();
		switch (colonizationType) {
		case EXPANSION:
			colonyRook = rook.expansion(condition);
			useAllConds = rook.getKingdom().size() < 2;
			break;
		case IMMIGRATION_AND_FOUNDATION:
			colonyRook = rook.immigrationAndFoundation(coRook, mBp, mPlacesCoRelation);
			break;
		default:
			colonyRook = null;
		}
		mLogger.debug("Applied: [%s] to Rook: %s with colonizer: [%s]", colonizationType, rook, condition);
		if (colonyRook != null) {
			mLogger.debug("Constructed new Rook: %s", colonyRook);
		}
		return new Pair<>(colonyRook, useAllConds);
	}

	private Rook<PLACE, LETTER> legislate(final Condition<LETTER, PLACE> condition, final Rook<PLACE, LETTER> rook) {
		if (rook.getLaw().getConditions().contains(condition)) {
			return null;
		}
		final boolean colonizer = isColonizer(condition);
		final CoRook<PLACE, LETTER> coRook = new CoRook<>(condition, rook, mBp, colonizer, mPlacesCoRelation);
		Rook<PLACE, LETTER> colonyRook;
		final LegislationType legislationType = coRook.getLegislation();
		switch (legislationType) {
		case APPROVAL:
			colonyRook = rook.approval(condition);
			break;
		case ENACTMENT:
			colonyRook = rook.enactment(coRook);
			break;
		case RATIFICATION:
			colonyRook = rook.ratification(coRook);
			break;
		case DISCRIMINATION:
			colonyRook = rook.discrimination(coRook);
			break;
		default:
			colonyRook = null;
		}
		mLogger.debug("Applied: [%s] to Rook: %s with colonizer: [%s]", legislationType, rook, condition);
		if (colonyRook != null) {
			mLogger.debug("Constructed new Rook: %s", colonyRook);
		}
		return colonyRook;
	}

	private boolean isColonizer(final Condition<LETTER, PLACE> condition) {
		return mOrigConds.contains(condition);
	}

	public Crown<PLACE, LETTER> getCrown() {
		return mCrown;
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		public static final String SETTLEMENT_TIME = "settlement time";
		public static final String CROWN_COMPUTATION_TIME = "crown computation time";
		public static final String CROWN_REFURBISHMENT_TIME = "crown refurbishment time";
		public static final String NUM_KINGDOMS = "number of kingdoms in crown";
		public static final String ASSERTION_SIZE = "crown assertion size";
		public static final String CROWN_SIZE = "crown size";
		public static final String REALM_KINGDOM = "number of realms per kingdom";

		private final TimeTracker mSettlementTimer = new TimeTracker();
		private final TimeTracker mCrownTimer = new TimeTracker();
		private final TimeTracker mRefurbishmentTimer = new TimeTracker();
		private long mNumKingdoms;
		private long mAssertionSize;
		private long mCrownSize;
		private final MinMaxMed mRealmsPerKingdom = new MinMaxMed();

		public Statistics() {
			declare(SETTLEMENT_TIME, () -> mSettlementTimer, KeyType.TT_TIMER_MS);
			declare(CROWN_COMPUTATION_TIME, () -> mCrownTimer, KeyType.TT_TIMER_MS);
			declare(CROWN_REFURBISHMENT_TIME, () -> mRefurbishmentTimer, KeyType.TT_TIMER_MS);
			declare(NUM_KINGDOMS, () -> mNumKingdoms, KeyType.COUNTER);
			declare(ASSERTION_SIZE, () -> mAssertionSize, KeyType.COUNTER);
			declare(CROWN_SIZE, () -> mCrownSize, KeyType.COUNTER);
			declareMinMaxMed(REALM_KINGDOM, mRealmsPerKingdom);
		}

		private <T> T measureSettlement(final Supplier<T> runner) {
			return mSettlementTimer.measure(runner);
		}

		private <T> T measureCrownComputation(final Supplier<T> runner) {
			return mCrownTimer.measure(runner);
		}

		private <T> T measureRefurbishment(final Supplier<T> runner) {
			return mRefurbishmentTimer.measure(runner);
		}

		private void reportCrown(final Crown<?, ?> crown) {
			mNumKingdoms = crown.getNumKingdoms();
			mAssertionSize = crown.getAssertionSize();
			mCrownSize = crown.getCrownSize();
			mRealmsPerKingdom.report(crown.getRooks(), r -> r.getKingdom().size());
		}
	}
}
