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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class EmpireComputation<L, P> {
	public static final boolean SORT_TRANSITIONS = false;

	private final ILogger mLogger;

	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProduct;
	private final PlacesCoRelation<P> mCoRelation;

	private final EmpireAnnotation<P> mEmpire;

	public enum SuccessorComputationMode {
		CO_RELATION, NO_CORELATION
	}

	private final SuccessorComputationMode mMode;

	public EmpireComputation(final IUltimateServiceProvider services, final IPetriNet<L, P> net,
			final PlacesCoRelation<P> coRelation,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> product) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.ERROR);

		mNet = net;
		mProduct = product;
		mCoRelation = coRelation;
		mMode = SuccessorComputationMode.CO_RELATION;

		final var mTerrPlacePairs = symbolicExecution();
		final var territoryLawPairs =
				mTerrPlacePairs.stream().map(p -> new Pair<>(p.getFirst(), p.getSecond())).collect(Collectors.toSet());
		mEmpire = new EmpireAnnotation<>(territoryLawPairs);
	}

	public EmpireComputation(final IUltimateServiceProvider services, final IPetriNet<L, P> net,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> product) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.ERROR);

		mNet = net;
		mProduct = product;
		mCoRelation = null;
		mMode = SuccessorComputationMode.NO_CORELATION;

		final var mTerrPlacePairs = symbolicExecution();
		final var territoryLawPairs =
				mTerrPlacePairs.stream().map(p -> new Pair<>(p.getFirst(), p.getSecond())).collect(Collectors.toSet());
		mEmpire = new EmpireAnnotation<>(territoryLawPairs);
	}

	public EmpireAnnotation<P> getEmpire() {
		return mEmpire;
	}

	public IStatisticsDataProvider getStatistics() {
		final var statistics = new CrownsEmpire.Statistics();
		statistics.reportEmpire(mEmpire);
		return statistics;
	}

	private Set<Pair<Territory<P>, IPredicate>> symbolicExecution() {
		final var queue = new ArrayDeque<GraphNode<P>>();
		final var resultNodes = new HashSet<GraphNode<P>>();

		queue.offer(getInitialNode());

		while (!queue.isEmpty()) {
			var node = queue.poll();
			var pair = node.getPair();
			if (resultNodes.contains(node)) {
				continue;
			}

			var territory = pair.getFirst();
			var lawPlace = pair.getSecond();

			final var enabledTransitions = getEnabledTransitions(territory, lawPlace);
			if (enabledTransitions.isEmpty()) {
				resultNodes.add(node);
				continue;
			}
			final var extendingTransitions = getExtendingTransitions(node, enabledTransitions);
			final var replacementTransitions = DataStructureUtils.difference(enabledTransitions, extendingTransitions);
			final var necessaryBridgeTransitions = getNecessaryBridgeTransitions(node, extendingTransitions);
			final var simpleExtendingTransitions =
					DataStructureUtils.difference(extendingTransitions, necessaryBridgeTransitions);
			var subsumes = false;
			for (final var transition : simpleExtendingTransitions) {
				final Pair<Territory<P>, IPredicate> successor = getExtensionPair(pair, transition);
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
				node = new GraphNode<>(pair, node.getBridgeBystanders());
			}

			if (subsumes) {
				queue.add(new GraphNode<>(pair, node.getBridgeBystanders()));
				// First fully extend the territory before any replacement
				continue;
			}

			if (!subsumes && necessaryBridgeTransitions.isEmpty() && replacementTransitions.isEmpty()) {
				resultNodes.add(node);
			}

			if (!necessaryBridgeTransitions.isEmpty()) {
				resultNodes.add(node);
			}

			for (final var transition : necessaryBridgeTransitions) {
				final var successor = getReplacementPair(pair, transition);
				if (successor == null) {
					continue;
				}
				final var successorNode = new GraphNode<>(successor, transition);
				queue.add(successorNode);

			}

			for (final var transition : replacementTransitions) {

				final var successor = getReplacementPair(pair, transition);
				if (successor == null) {
					resultNodes.add(node);
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
				final var successorNode = new GraphNode<>(successor, transition);
				queue.offer(successorNode);
				resultNodes.add(node);
			}

		}
		return resultNodes.stream().map(GraphNode::getPair).collect(Collectors.toSet());
	}

	private GraphNode<P> getInitialNode() {
		final var initialLaw = DataStructureUtils.getOneAndOnly(mProduct.getInitialStates(), "initial law place");
		final var regions = mNet.getInitialPlaces().stream().map(p -> new Region<>(ImmutableSet.singleton(p)))
				.collect(ImmutableSet.collector());
		final var pair = new Pair<>(new Territory<>(regions), initialLaw);
		return new GraphNode<>(pair);
	}

	private Set<Transition<L, P>> getEnabledTransitions(final Territory<P> territory, final IPredicate lawPlace) {
		final var enabledTransitions = territory.getEnabledTransitions(mNet).collect(Collectors.toSet());
		final var notBotTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : enabledTransitions) {
			final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
			IPredicate newLawPlace = lawPlace;
			if (succLaw.iterator().hasNext()) {
				newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
			} else {
				mLogger.warn("No successor law for transition: %s and law: %s", transition, lawPlace);
			}
			if (!SmtUtils.isFalseLiteral(newLawPlace.getFormula())) {
				notBotTransitions.add(transition);
			}
		}
		return notBotTransitions;
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

	private Pair<Territory<P>, IPredicate> getExtensionPair(final Pair<Territory<P>, IPredicate> pair,
			final Transition<L, P> transition) {
		final var territory = pair.getFirst();
		final var law = pair.getSecond();
		final var regions = territory.getBystanders(transition);
		final var remainingRegions = DataStructureUtils.difference(territory.getRegions(), regions);
		final var extendedRegions = extendRegions(territory, law, law, transition.getPredecessors(),
				transition.getSuccessors(), remainingRegions);
		regions.addAll(extendedRegions);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new Pair<>(newTerritory, law);
	}

	private Set<Region<P>> extendRegions(final Territory<P> territory, final IPredicate lawPlace,
			final IPredicate newLawPlace, final Set<P> predecessors, final Set<P> successors,
			final Set<Region<P>> remainingRegions) {
		final Set<Region<P>> extendedRegions = new HashSet<>();
		if (lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1) {
			final Region<P> match = DataStructureUtils.getOneAndOnly(remainingRegions, "remaining region");
			extendedRegions.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), successors))));
			return extendedRegions;
		}
		for (final P placeP : successors) {
			final var match = findMatchingRegion(remainingRegions, placeP, territory);
			remainingRegions.remove(match);
			extendedRegions
					.add(new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), Set.of(placeP)))));
		}
		return extendedRegions;
	}

	private Pair<Territory<P>, IPredicate> getReplacementPair(final Pair<Territory<P>, IPredicate> pair,
			final Transition<L, P> transition) {
		final var territory = pair.getFirst();
		final var lawPlace = pair.getSecond();
		final var successors = transition.getSuccessors();

		final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
		IPredicate newLawPlace = lawPlace;
		if (succLaw.iterator().hasNext()) {
			newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		} else {
			mLogger.warn("No successor law for transition: %s and law: %s", transition, lawPlace);
		}

		var regions = territory.getBystanders(transition);

		regions = replaceRegions(transition, regions);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new Pair<>(newTerritory, newLawPlace);
	}

	private Set<Region<P>> replaceRegions(final Transition<L, P> transition, final Set<Region<P>> bystanders) {
		final var regions = new HashSet<>(bystanders);
		final var successors = transition.getSuccessors();
		for (final var succ : successors) {
			regions.add(new Region<>(ImmutableSet.singleton(succ)));
		}
		return regions;
	}

	private boolean isExtendingTransition(final Territory<P> territory, final IPredicate lawPlace,
			final IPredicate newLawPlace, final Transition<L, P> transition) {
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

	private Set<Transition<L, P>> getExtendingTransitions(final GraphNode<P> node,
			final Set<Transition<L, P>> transitions) {
		final var pair = node.getPair();
		final var territory = pair.getFirst();
		final var lawPlace = pair.getSecond();
		final var extendingTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : transitions) {
			final var succLaw = mProduct.internalSuccessors(lawPlace, transition.getSymbol());
			IPredicate newLawPlace = lawPlace;
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

	private Set<Transition<L, P>> getNecessaryBridgeTransitions(final GraphNode<P> node,
			final Set<Transition<L, P>> transitions) {
		final var necessaryTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : transitions) {
			if (node.isNecessaryBridge(transition)) {
				necessaryTransitions.add(transition);
			}
		}
		return necessaryTransitions;
	}
}
