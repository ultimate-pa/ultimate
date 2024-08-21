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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class PostProcessing<P> {
	private final Set<Pair<Territory<P>, Set<P>>> mPairs;
	private final Set<Pair<Territory<P>, IPredicate>> mProcessedPairs;
	private final BasicPredicateFactory mFactory;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final Map<IPredicate, Set<P>> mPredicatePlacesMap = new HashMap<>();
	private final ILogger mLogger;

	public PostProcessing(final IUltimateServiceProvider services, final Set<Pair<Territory<P>, Set<P>>> pairs,
			final BasicPredicateFactory factory, final MonolithicImplicationChecker implicationChecker,
			final Function<P, IPredicate> assertionPlace2Predicate) {
		mPairs = pairs;
		mFactory = factory;
		mImplicationChecker = implicationChecker;
		mLogger = services.getLoggingService().getLogger(getClass());
		final var processedPairs = postProcessing();
		mProcessedPairs = constructPredicatePairs(processedPairs, assertionPlace2Predicate);
	}

	private Set<Pair<Territory<P>, IPredicate>> constructPredicatePairs(final Set<Pair<Territory<P>, Set<P>>> pairs,
			final Function<P, IPredicate> assertionPlace2Predicate) {
		final var result = new HashSet<Pair<Territory<P>, IPredicate>>();
		final var predicatePlaceMap = new HashMap<P, IPredicate>();
		for (final Pair<Territory<P>, Set<P>> pair : pairs) {
			final var predicates = pair.getSecond().stream()
					.map(p -> predicatePlaceMap.computeIfAbsent(p, p1 -> assertionPlace2Predicate.apply(p1)))
					.collect(Collectors.toSet());
			final var lawDisjunction = mFactory.or(predicates);
			result.add(new Pair<>(pair.getFirst(), lawDisjunction));
			mPredicatePlacesMap.put(lawDisjunction, pair.getSecond());
		}
		return result;
	}

	private Set<Pair<Territory<P>, Set<P>>> postProcessing() {
		final var territoriesByLenght = sortTerritoriesByLength();
		final var processedPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		for (final Entry<Integer, HashSet<Pair<Territory<P>, Set<P>>>> entry : territoriesByLenght.entrySet()) {
			final var pairs = entry.getValue();
			final var newPairs = processSet(pairs);
			processedPairs.addAll(newPairs);
		}
		return processedPairs;
	}

	private Set<Pair<Territory<P>, Set<P>>> processSet(final Set<Pair<Territory<P>, Set<P>>> pairs) {
		final var pairsList = new ArrayList<>(pairs);
		final var newPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		final var removedPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		final var sharedPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		var overlapInSet = false;
		for (int i = 0; i < pairsList.size() - 1; i++) {
			final var pair = pairsList.get(i);
			final var overlappingPairs = getOverlappingPairs(pair, pairsList.subList(i + 1, pairsList.size()));
			if (overlappingPairs.isEmpty()) {
				continue;
			}
			overlapInSet = true;
			removedPairs.add(pair);
			removedPairs.addAll(overlappingPairs);
			final var splitPairs = getSplitPairs(pair, overlappingPairs);
			newPairs.addAll(splitPairs.getFirst());
			newPairs.addAll(splitPairs.getSecond());
			sharedPairs.addAll(splitPairs.getFirst());
		}
		if (!overlapInSet) {
			return pairs;
		}
		mLogger.log(LogLevel.DEBUG, "Recursively process sets:\n%s", newPairs);
		// final var filteredPairs = filterSubsumedPairs(newPairs);
		// final var result = processSet(filteredPairs);
		// result.addAll(sharedPairs);
		newPairs.addAll(DataStructureUtils.difference(pairs, removedPairs));
		return filterSubsumedPairs(newPairs);
	}

	private Set<Pair<Territory<P>, Set<P>>> filterSubsumedPairs(final Set<Pair<Territory<P>, Set<P>>> pairs) {
		final var subsumedPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		for (final Pair<Territory<P>, Set<P>> pair1 : pairs) {
			final var terr = pair1.getFirst();
			final var law = pair1.getSecond();
			for (final Pair<Territory<P>, Set<P>> pair2 : pairs) {
				if (pair1.equals(pair2)) {
					continue;
				}
				final var equalLaw = pair2.getSecond().containsAll(law);
				if (equalLaw && pair2.getFirst().subsumes(terr)) {
					subsumedPairs.add(pair1);
				}
			}
		}
		return DataStructureUtils.difference(pairs, subsumedPairs);
	}

	private HashRelation<Integer, Pair<Territory<P>, Set<P>>> sortTerritoriesByLength() {
		final var result = new HashRelation<Integer, Pair<Territory<P>, Set<P>>>();
		for (final Pair<Territory<P>, Set<P>> pair : mPairs) {
			result.addPair(pair.getFirst().getRegions().size(), pair);
		}
		return result;
	}

	private Set<Pair<Territory<P>, Set<P>>> getOverlappingPairs(final Pair<Territory<P>, Set<P>> pair,
			final List<Pair<Territory<P>, Set<P>>> potentialPairs) {
		final var result = new HashSet<Pair<Territory<P>, Set<P>>>();
		final var terr1 = pair.getFirst();
		final var law1 = pair.getSecond();
		for (final Pair<Territory<P>, Set<P>> pair2 : potentialPairs) {
			final var terr2 = pair2.getFirst();
			final var law2 = pair2.getSecond();
			final var equivalentLaws = law1.equals(law2);
			mLogger.log(LogLevel.DEBUG, "Law 1: %s, Law 2: %s, Equals: %s", law1, law2, equivalentLaws);
			if (equivalentLaws) {
				continue;
			}
			final var overlapping = checkOverlappingRegions(terr1, terr2);
			if (overlapping) {
				result.add(pair2);
			}
		}
		return result;
	}

	private boolean checkOverlappingRegions(final Territory<P> terr1, final Territory<P> terr2) {
		if (terr1.equals(terr2)) {
			return true;
		}
		final Set<Region<P>> potentialOverlapping = new HashSet<>(terr2.getRegions());
		for (final Region<P> region : terr1.getRegions()) {
			final var overlapping = getMatchingRegions(region, potentialOverlapping);
			if (overlapping.size() != 1) {
				return false;
			}
			potentialOverlapping.removeAll(overlapping);
		}
		mLogger.log(LogLevel.DEBUG, "Check overlap for: \n%s and %s", terr1, terr2);
		return true;
	}

	private Set<Region<P>> getMatchingRegions(final Region<P> region, final Set<Region<P>> regions) {
		return regions.stream()
				.filter(r -> !DataStructureUtils.haveEmptyIntersection(r.getPlaces(), region.getPlaces()))
				.collect(Collectors.toSet());
	}

	private Pair<Set<Pair<Territory<P>, Set<P>>>, Set<Pair<Territory<P>, Set<P>>>>
			getSplitPairs(final Pair<Territory<P>, Set<P>> pair, final Set<Pair<Territory<P>, Set<P>>> pairs) {
		final var sharedPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		final var remainingPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		for (final Pair<Territory<P>, Set<P>> p2 : pairs) {
			sharedPairs.add(getSharedPair(pair, p2));
			remainingPairs.addAll(getRemainingPairs(pair, p2));
			remainingPairs.addAll(getRemainingPairs(p2, pair));
		}
		return new Pair<>(sharedPairs, remainingPairs);
	}

	private Pair<Territory<P>, Set<P>> getSharedPair(final Pair<Territory<P>, Set<P>> pair1,
			final Pair<Territory<P>, Set<P>> pair2) {
		final var pair2Regions = new HashSet<>(pair2.getFirst().getRegions());
		final var newLaw = DataStructureUtils.union(pair1.getSecond(), pair2.getSecond());
		final var newRegions = new HashSet<Region<P>>();
		for (final Region<P> region : pair1.getFirst().getRegions()) {
			final var matching = getMatchingRegions(region, pair2Regions);
			final var matchingRegion = DataStructureUtils.getOneAndOnly(matching, "Overlapping Region");
			final var newRegion = new Region<>(
					ImmutableSet.of(DataStructureUtils.intersection(region.getPlaces(), matchingRegion.getPlaces())));
			newRegions.add(region);
			pair2Regions.removeAll(matching);
		}
		final var territory = new Territory<>(ImmutableSet.of(newRegions));
		return new Pair<>(territory, newLaw);
	}

	private Set<Pair<Territory<P>, Set<P>>> getRemainingPairs(final Pair<Territory<P>, Set<P>> pair1,
			final Pair<Territory<P>, Set<P>> pair2) {
		final var remainingPairs = new HashSet<Pair<Territory<P>, Set<P>>>();
		for (final Region<P> region : pair1.getFirst().getRegions()) {
			final var matching = getMatchingRegions(region, pair2.getFirst().getRegions());
			final var matchingRegion = DataStructureUtils.getOneAndOnly(matching, "Overlapping Region");
			final var difference = DataStructureUtils.difference(region.getPlaces(), matchingRegion.getPlaces());
			if (difference.isEmpty()) {
				continue;
			}
			final var differenceRegion = new Region<>(ImmutableSet.of(difference));
			var remainingRegions = DataStructureUtils.difference(pair1.getFirst().getRegions(), Set.of(region));
			remainingRegions = DataStructureUtils.union(remainingRegions, Set.of(differenceRegion));
			final var territory = new Territory<>(ImmutableSet.of(remainingRegions));
			remainingPairs.add(new Pair<>(territory, pair1.getSecond()));
		}
		return remainingPairs;
	}

	public Set<Pair<Territory<P>, IPredicate>> getProcessedPairs() {
		return mProcessedPairs;
	}

	public Map<IPredicate, Set<P>> getPredicatePlacesMap() {
		return mPredicatePlacesMap;
	}
}
