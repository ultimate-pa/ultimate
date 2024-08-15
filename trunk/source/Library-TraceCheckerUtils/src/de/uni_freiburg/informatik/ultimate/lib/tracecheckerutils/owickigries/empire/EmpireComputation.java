/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class EmpireComputation<L, P> {
	public static final boolean SORT_TRANSITIONS = false;

	private final ILogger mLogger;

	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, P> mProduct;
	private final PlacesCoRelation<P> mCoRelation;

	private final BasicPredicateFactory mFactory;
	private final MonolithicHoareTripleChecker mHc;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final Function<P, IPredicate> mPlaceToPredicate;

	private final EmpireAnnotation<P> mEmpire;
	private final Map<P, IPredicate> mPlacePredicateMap = new HashMap<>();

	public EmpireComputation(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final IPetriNet<L, P> net, final PlacesCoRelation<P> coRelation,
			final Function<P, IPredicate> assertionPlace2Predicate,
			final INwaOutgoingLetterAndTransitionProvider<L, P> product,
			final MonolithicHoareTripleChecker hoareTripleChecker,
			final MonolithicImplicationChecker implicationChecker) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.INFO);

		mNet = net;
		mProduct = product;
		mCoRelation = coRelation;

		mFactory = predicateFactory;
		mHc = hoareTripleChecker;
		mImplicationChecker = implicationChecker;
		mPlaceToPredicate = assertionPlace2Predicate;

		final var mTerrPlacePairs = symbolicExecution();
		final var lawMap = mTerrPlacePairs.stream()
				.map(p -> new Pair<>(p.getFirst(),
						mPlacePredicateMap.computeIfAbsent(p.getSecond(), assertionPlace2Predicate)))
				.collect(Collectors.toSet());
		mEmpire = new EmpireAnnotation<>(lawMap);
	}

	public EmpireAnnotation<P> getEmpire() {
		return mEmpire;
	}

	public IStatisticsDataProvider getStatistics() {
		final var statistics = new CrownsEmpire.Statistics();
		statistics.reportEmpire(mEmpire);
		return statistics;
	}

	private Set<Pair<Territory<P>, P>> symbolicExecution() {
		final var result = new HashSet<Pair<Territory<P>, P>>();
		final var bridgeTerritories = new HashRelation<Pair<Territory<P>, P>, Pair<Territory<P>, P>>();

		final var queue = new ArrayDeque<Pair<Territory<P>, P>>();
		queue.offer(getInitialPair());

		while (!queue.isEmpty()) {
			final var pair = queue.poll();
			if (result.contains(pair)) {
				continue;
			}

			final var territory = pair.getFirst();
			final var lawPlace = pair.getSecond();

			final var successors = new ArrayList<Pair<Territory<P>, P>>();
			boolean subsumed = false;
			final Stream<Transition<L, P>> enabledTransitions = getEnabledTransitions(territory, lawPlace);
			for (final var transition : (Iterable<Transition<L, P>>) enabledTransitions::iterator) {

				final var successor = computeSuccessor(territory, lawPlace, transition);
				if (successor == null) {
					continue;
				}
				final var succTerritory = successor.getFirst();
				final var succLawPlace = successor.getSecond();
				mLogger.debug("successor of %s under transitions %s is %s", pair, transition, successor);
				final var numBystanders = territory.getRegions().size() - transition.getPredecessors().size();

				if (lawPlace.equals(succLawPlace) && territory.equals(succTerritory)) {
					// do nothing
					mLogger.debug("\t--> self loop; skipping...");
				} else if (lawPlace.equals(succLawPlace) && succTerritory.subsumes(territory)) {
					final var bridgePre = bridgeTerritories.getImage(pair);
					final var importantBridge =
							isImportantBridge(pair, successor, bridgePre, transition.getSuccessors());
					if (importantBridge) {
						result.add(pair);
						bridgeTerritories.removeDomainElement(pair);
					}
					subsumed = true;

					// TODO instead of discarding successors for other transitions, should we reuse them?
					// TODO e.g. if size changes, the successor of successor will be the same, no need to discard
					// TODO and maybe in other cases, we can still augment them?
					successors.clear();

					// TODO remember that this transition was already considered; do not consider again for successor
					queue.offer(successor);

					mLogger.debug("\t--> subsumption; abandoning %s...", pair);
					break;
				} else if (numBystanders > 0 && !lawPlace.equals(succLawPlace)) {
					bridgeTerritories.addPair(successor, pair);
					queue.offer(successor);
				} else {
					successors.add(successor);
					mLogger.debug("\t--> regular successor; adding...");
				}
			}

			if (!subsumed) {
				result.add(pair);
				bridgeTerritories.removeDomainElement(pair);
			}
			for (final var succ : successors) {
				queue.offer(succ);
			}
		}
		return result;
	}

	private boolean isImportantBridge(final Pair<Territory<P>, P> prePair, final Pair<Territory<P>, P> succPair,
			final Set<Pair<Territory<P>, P>> bridgePairs, final Set<P> succPlaces) {
		if (bridgePairs.isEmpty()) {
			return false;
		}
		for (final Pair<Territory<P>, P> pair2 : bridgePairs) {
			final var bystanders =
					DataStructureUtils.intersection(prePair.getFirst().getRegions(), pair2.getFirst().getRegions());
			if (!succPair.getFirst().getRegions().containsAll(bystanders)) {
				final var allCorelated =
						succPlaces.stream().allMatch(p -> mCoRelation.getPlacesCorelation(p, pair2.getSecond()));
				return !allCorelated;
			}
		}
		return false;
	}

	private Pair<Territory<P>, P> getInitialPair() {
		final var initialLaw = DataStructureUtils.getOneAndOnly(mProduct.getInitialStates(), "initial law place");
		final var regions = mNet.getInitialPlaces().stream().map(p -> new Region<>(ImmutableSet.singleton(p)))
				.collect(ImmutableSet.collector());
		return new Pair<>(new Territory<>(regions), initialLaw);
	}

	private boolean enables(final Territory<P> territory, final P lawPlace, final Transition<L, P> transition) {
		// TODO how should we handle transitions where some successor places are not reachable in the refined net
		// (but may well be reachable in the original net?)
		// This can happen because we look at each automaton individually; another automaton not currently considered
		// may be responsible for the non-reachability.

		// mLogger.debug(" checking enabledness of transition %s (pred: %s, succ: %s) under %s and %s", transition,
		// transition.getPredecessors(), transition.getSuccessors(), territory, lawPlace);
		final var lawPredicate = mPlaceToPredicate.apply(lawPlace);
		final var htFalse = mHc.checkInternal(lawPredicate, (IInternalAction) transition.getSymbol(), mFactory.or());
		final var accepting = transition.getSuccessors().stream().anyMatch(p -> mNet.isAccepting(p));
		final var impliesFalse = mImplicationChecker.checkImplication(lawPredicate, false, mFactory.or(), false);
		if (!accepting && impliesFalse != Validity.VALID && htFalse == Validity.VALID) {
			return false;
		}
		final var regions = new HashSet<>(territory.getRegions());
		final var predecessors = transition.getPredecessors();
		for (final var place : predecessors) {
			final var it = regions.iterator();
			boolean found = false;
			while (!found && it.hasNext()) {
				final var region = it.next();
				if (region.contains(place)) {
					found = true;
					it.remove();
				}
			}
			if (!found) {
				// mLogger.debug(" --> rejected because predecessor %s not in any region", place);
				return false;
			}
		}
		// mLogger.debug(" --> enabled!");
		return true;
	}

	private Stream<Transition<L, P>> getEnabledTransitions(final Territory<P> territory, final P lawPlace) {
		final var mayPlaces = DataStructureUtils.union(territory.getPlaces(), Set.of(lawPlace));
		// mLogger.debug("Computing successors of %s and %s.", territory, lawPlace);
		// mLogger.debug(" may places: %s", mayPlaces);
		// mLogger.debug(" must places: %s", territory.getPlaces());
		return mNet.getSuccessorTransitionProviders(territory.getPlaces(), mayPlaces).stream()
				.flatMap(provider -> provider.getTransitions().stream()).filter(t -> enables(territory, lawPlace, t));
	}

	private Pair<Territory<P>, P> computeSuccessor(final Territory<P> territory, final P lawPlace,
			final Transition<L, P> transition) {
		// assert enables(territory, lawPlace, transition) : "transition is not enabled, cannot compute successor";

		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();

		// final var succLaw = mProduct.callSuccessors(lawPlace, transition.getSymbol());
		final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
		P newLawPlace = lawPlace;
		if (succLaw.iterator().hasNext()) {
			newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		} else {
			mLogger.warn("No successor law for transition: %s and law: %s", transition, lawPlace);
		}

		if (DataStructureUtils.haveNonEmptyIntersection(successors, mNet.getAcceptingPlaces())) {
			mLogger.log(LogLevel.INFO, "Contains accepting places");
		}

		final var regions = new HashSet<Region<P>>();

		// add bystanders
		for (final var region : territory.getRegions()) {
			if (DataStructureUtils.haveEmptyIntersection(region.getPlaces(), predecessors)) {
				regions.add(region);
			}
		}

		final var remainingRegions = DataStructureUtils.difference(new HashSet<>(territory.getRegions()), regions);
		final var extendingRegions =
				isExtendable(territory, lawPlace, newLawPlace, predecessors, successors, remainingRegions);
		if (extendingRegions != null) {
			regions.addAll(extendingRegions);
		} else {
			for (final var succ : successors) {
				regions.add(new Region<>(ImmutableSet.singleton(succ)));
			}
		}

		// TODO unify region instances
		// TODO unify Territory instances
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new Pair<>(newTerritory, newLawPlace);
	}

	private Region<P> findMatchingRegion(final Collection<Region<P>> candidates, final P place,
			final Territory<P> territory) {
		Region<P> chosen = null;
		for (final var region : candidates) {
			if (isNegativelyCorelated(region, place)) {
				chosen = region;
				break;
			}
		}
		if (chosen == null) {
			return null;
		}

		for (final var region : territory.getRegions()) {
			if (region.equals(chosen)) {
				continue;
			}
			if (!isPositivelyCorelated(region, place)) {
				return null;
			}
		}
		return chosen;
	}

	private boolean isNegativelyCorelated(final Region<P> region, final P place) {
		return region.contains(place)
				|| region.getPlaces().stream().allMatch(p -> !mCoRelation.getPlacesCorelation(place, p));
	}

	private boolean isPositivelyCorelated(final Region<P> region, final P place) {
		return !region.contains(place)
				&& region.getPlaces().stream().allMatch(p -> mCoRelation.getPlacesCorelation(place, p));
	}

	private Set<Region<P>> isExtendable(final Territory<P> territory, final P lawPlace, final P newLawPlace,
			final Set<P> predecessors, final Set<P> successors, final Set<Region<P>> remainingRegions) {
		final Set<Region<P>> expandedRegions = new HashSet<>();
		if (lawPlace != newLawPlace || predecessors.size() != successors.size()) {
			return null;
		} else if (lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1) {
			final Region<P> match = DataStructureUtils.getOneAndOnly(remainingRegions, "remaining region");
			expandedRegions.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), successors))));
			return expandedRegions;
		}
		for (final P placeP : successors) {
			final var match = findMatchingRegion(remainingRegions, placeP, territory);
			if (match == null) {
				return null;
			}
			remainingRegions.remove(match);
			expandedRegions
					.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), Set.of(placeP)))));
		}
		return expandedRegions;
	}

	public Map<IPredicate, P> getPredicatePlaceMap() {
		return mPlacePredicateMap.entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
	}
}
