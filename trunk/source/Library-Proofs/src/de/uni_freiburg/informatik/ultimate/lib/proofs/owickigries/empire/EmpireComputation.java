/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Matthias Zumkeller
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
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
	private final Map<IPredicate, Set<P>> mPredicatePlacesMap;

	public enum SuccessorComputationMode {
		CO_RELATION, NO_CORELATION
	}

	private final SuccessorComputationMode mMode;

	public EmpireComputation(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final IPetriNet<L, P> net, final PlacesCoRelation<P> coRelation,
			final Function<P, IPredicate> assertionPlace2Predicate,
			final INwaOutgoingLetterAndTransitionProvider<L, P> product,
			final MonolithicHoareTripleChecker hoareTripleChecker,
			final MonolithicImplicationChecker implicationChecker) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.ERROR);

		mNet = net;
		mProduct = product;
		mCoRelation = coRelation;
		mMode = SuccessorComputationMode.CO_RELATION;

		mFactory = predicateFactory;
		mHc = hoareTripleChecker;
		mImplicationChecker = implicationChecker;
		mPlaceToPredicate = assertionPlace2Predicate;

		final var mTerrPlacePairs = symbolicExecution();
		final var territorySetPairs = mTerrPlacePairs.stream().map(p -> new Pair<>(p.getFirst(), Set.of(p.getSecond())))
				.collect(Collectors.toSet());
		final var postProcessing = new PostProcessing<>(services, territorySetPairs, predicateFactory,
				implicationChecker, assertionPlace2Predicate);
		final var processedPairs = postProcessing.getProcessedPairs();
		mPredicatePlacesMap = postProcessing.getPredicatePlacesMap();
		mEmpire = new EmpireAnnotation<>(processedPairs);
	}

	public EmpireComputation(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final IPetriNet<L, P> net, final Function<P, IPredicate> assertionPlace2Predicate,
			final INwaOutgoingLetterAndTransitionProvider<L, P> product,
			final MonolithicHoareTripleChecker hoareTripleChecker,
			final MonolithicImplicationChecker implicationChecker) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.ERROR);

		mNet = net;
		mProduct = product;
		mCoRelation = null;
		mMode = SuccessorComputationMode.NO_CORELATION;

		mFactory = predicateFactory;
		mHc = hoareTripleChecker;
		mImplicationChecker = implicationChecker;
		mPlaceToPredicate = assertionPlace2Predicate;

		final var mTerrPlacePairs = symbolicExecution();
		final var territorySetPairs = mTerrPlacePairs.stream().map(p -> new Pair<>(p.getFirst(), Set.of(p.getSecond())))
				.collect(Collectors.toSet());
		final var postProcessing = new PostProcessing<>(services, territorySetPairs, predicateFactory,
				implicationChecker, assertionPlace2Predicate);
		final var processedPairs = postProcessing.getProcessedPairs();
		mPredicatePlacesMap = postProcessing.getPredicatePlacesMap();
		mEmpire = new EmpireAnnotation<>(processedPairs);
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
		final var queue = new ArrayDeque<Pair<Territory<P>, P>>();
		final BridgePairs<P> bridgePairs = new BridgePairs<>();

		queue.offer(getInitialPair());

		while (!queue.isEmpty()) {
			var pair = queue.poll();
			if (result.contains(pair)) {
				continue;
			}

			var territory = pair.getFirst();
			var lawPlace = pair.getSecond();

			final var enabledTransitions = getEnabledTransitions(territory, lawPlace).collect(Collectors.toSet());
			final var extendingTransitions = getExtendingTransitions(pair, enabledTransitions);
			final var replacementTransitions = DataStructureUtils.difference(enabledTransitions, extendingTransitions);
			var subsumes = false;
			for (final var transition : extendingTransitions) {
				Pair<Territory<P>, P> successor;

				if (bridgePairs.isNecessaryBridge(pair, transition)) {
					result.add(pair);
					final var bystanders = territory.getBystanders(transition);
					final var bridgeSuccessor = replaceRegions(transition, bystanders);
					successor = new Pair<>(new Territory<>(ImmutableSet.of(bridgeSuccessor)), lawPlace);
					bridgePairs.addBridge(successor, pair, transition);
					queue.add(successor);
					continue;
				}
				successor = computeSuccessor(territory, lawPlace, transition);
				if (successor == null) {
					continue;
				}

				final var succTerritory = successor.getFirst();
				final var succLawPlace = successor.getSecond();
				mLogger.debug("successor of %s under transitions %s is %s", pair, transition, successor);

				if (lawPlace.equals(succLawPlace) && territory.equals(succTerritory)) {
					// do nothing
					mLogger.debug("\t--> self loop; skipping...");
					continue;
				}
				subsumes = true;
				pair = successor;
				territory = pair.getFirst();
				lawPlace = pair.getSecond();
			}

			if (subsumes) {
				queue.add(pair);
				// First fully extend the territory before any replacement
				continue;
			}

			if (extendingTransitions.isEmpty() && replacementTransitions.isEmpty()) {
				result.add(pair);
			}

			for (final var transition : replacementTransitions) {

				final var successor = computeSuccessor(territory, lawPlace, transition);
				if (successor == null) {
					result.add(pair);
					continue;
				}
				final var succTerritory = successor.getFirst();
				final var succLawPlace = successor.getSecond();
				mLogger.debug("successor of %s under transitions %s is %s", pair, transition, successor);

				if (lawPlace.equals(succLawPlace) && territory.equals(succTerritory)) {
					// do nothing
					mLogger.debug("\t--> self loop; skipping...");
					continue;
				}

				queue.offer(successor);
				result.add(pair);
				bridgePairs.addBridge(successor, pair, transition);
			}

		}
		return result;
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
				return false;
			}
		}
		return true;
	}

	private Stream<Transition<L, P>> getEnabledTransitions(final Territory<P> territory, final P lawPlace) {
		final var mayPlaces = DataStructureUtils.union(territory.getPlaces(), Set.of(lawPlace));
		return mNet.getSuccessorTransitionProviders(territory.getPlaces(), mayPlaces).stream()
				.flatMap(provider -> provider.getTransitions().stream()).filter(t -> enables(territory, lawPlace, t));
	}

	private Pair<Territory<P>, P> computeSuccessor(final Territory<P> territory, final P lawPlace,
			final Transition<L, P> transition) {

		final var successors = transition.getSuccessors();

		if (mNet.isAccepting(new Marking<>(successors))) {
			return null;
		}

		final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
		P newLawPlace = lawPlace;
		if (succLaw.iterator().hasNext()) {
			newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		} else {
			mLogger.warn("No successor law for transition: %s and law: %s", transition, lawPlace);
		}

		final var predecessors = transition.getPredecessors();

		var regions = territory.getBystanders(transition);

		final var remainingRegions = DataStructureUtils.difference(new HashSet<>(territory.getRegions()), regions);

		// Extend existing regions if possible
		final var extendedRegions =
				extendRegions(territory, lawPlace, newLawPlace, predecessors, successors, remainingRegions);
		if (extendedRegions != null) {
			regions.addAll(extendedRegions);
		} else {
			regions = replaceRegions(transition, regions);
		}
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

	private Set<Region<P>> extendRegions(final Territory<P> territory, final P lawPlace, final P newLawPlace,
			final Set<P> predecessors, final Set<P> successors, final Set<Region<P>> remainingRegions) {
		final Set<Region<P>> extendedRegions = new HashSet<>();
		if (lawPlace != newLawPlace || predecessors.size() != successors.size()) {
			return null;
		} else if (lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1) {
			final Region<P> match = DataStructureUtils.getOneAndOnly(remainingRegions, "remaining region");
			extendedRegions.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), successors))));
			return extendedRegions;
		}
		if (mMode == SuccessorComputationMode.NO_CORELATION) {
			return null;
		}
		for (final P placeP : successors) {
			final var match = findMatchingRegion(remainingRegions, placeP, territory);
			if (match == null) {
				return null;
			}
			remainingRegions.remove(match);
			extendedRegions
					.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), Set.of(placeP)))));
		}
		return extendedRegions;
	}

	private Set<Region<P>> replaceRegions(final Transition<L, P> transition, final Set<Region<P>> bystanders) {
		final var regions = new HashSet<>(bystanders);
		final var successors = transition.getSuccessors();
		for (final var succ : successors) {
			regions.add(new Region<>(ImmutableSet.singleton(succ)));
		}
		return regions;
	}

	private boolean isExtendingTransition(final Territory<P> territory, final P lawPlace, final P newLawPlace,
			final Transition<L, P> transition) {
		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		if (lawPlace != newLawPlace || predecessors.size() != successors.size()) {
			return false;
		} else if (lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1) {
			return true;
		}
		if (mMode == SuccessorComputationMode.NO_CORELATION) {
			return false;
		}
		final var remainingRegions = territory.getRegions().stream()
				.filter(r -> DataStructureUtils.haveEmptyIntersection(r.getPlaces(), predecessors))
				.collect(Collectors.toSet());
		for (final P placeP : successors) {
			final var match = findMatchingRegion(remainingRegions, placeP, territory);
			if (match == null) {
				return false;
			}
			remainingRegions.remove(match);
		}
		return true;
	}

	private Set<Transition<L, P>> getExtendingTransitions(final Pair<Territory<P>, P> pair,
			final Set<Transition<L, P>> transitions) {
		final var territory = pair.getFirst();
		final var lawPlace = pair.getSecond();
		final var extendingTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : transitions) {
			final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
			P newLawPlace = lawPlace;
			if (succLaw.iterator().hasNext()) {
				newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
			} else {
				mLogger.warn("No successor law for transition: %s and law: %s", transition, lawPlace);
			}
			if (isExtendingTransition(territory, lawPlace, newLawPlace, transition)) {
				extendingTransitions.add(transition);
			}
		}
		return extendingTransitions;
	}

	public Map<IPredicate, Set<P>> getPredicatePlaceMap() {
		return mPredicatePlacesMap;
	}
}
