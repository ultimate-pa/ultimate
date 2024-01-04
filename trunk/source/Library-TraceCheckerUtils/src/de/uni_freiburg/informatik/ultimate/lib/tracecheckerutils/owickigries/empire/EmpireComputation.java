package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class EmpireComputation<L, P> {
	private final ILogger mLogger;

	private final IPetriNetSuccessorProvider<L, P> mRefinedNet;
	private final PlacesCoRelation<P> mCoRelation;

	private final Set<P> mOriginalPlaces;
	private final Set<P> mAssertionPlaces;
	private final List<Set<P>> mProofPlaces;

	private final EmpireAnnotation<P> mEmpire;

	public EmpireComputation(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final IPetriNetSuccessorProvider<L, P> refinedNet, final Set<P> originalPlaces,
			final List<Set<P>> proofPlaces, final PlacesCoRelation<P> coRelation,
			final Function<P, IPredicate> assertionPlace2Predicate) {
		mLogger = services.getLoggingService().getLogger(getClass());
		// mLogger.setLevel(LogLevel.INFO);

		mRefinedNet = refinedNet;
		mCoRelation = coRelation;

		mOriginalPlaces = originalPlaces;
		mProofPlaces = proofPlaces;
		mLogger.debug("proof places: %s", proofPlaces);
		mAssertionPlaces = proofPlaces.stream().flatMap(Set::stream).collect(Collectors.toSet());

		final var result = symbolicExecution();
		final var lawMap = result.stream().collect(Collectors.toMap(Pair::getFirst,
				pair -> assertionPlace2Predicate.apply(pair.getSecond()), predicateFactory::and));
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
		for (final var proof : mProofPlaces) {
			mLogger.debug("symbolic execution on predicates %s", proof);
			mLogger.debug("----------------------------------------------");
			result.addAll(symbolicExecution(proof));
			mLogger.debug("==============================================");
			mLogger.debug("");
			break;
		}
		return result;
	}

	private Set<Pair<Territory<P>, P>> symbolicExecution(final Set<P> proofPlaces) {
		final var result = new HashSet<Pair<Territory<P>, P>>();

		final var queue = new ArrayDeque<Pair<Territory<P>, P>>();
		queue.offer(getInitialPair(proofPlaces));

		while (!queue.isEmpty()) {
			final var pair = queue.poll();
			if (result.contains(pair)) {
				continue;
			}

			final var territory = pair.getFirst();
			final var lawPlace = pair.getSecond();

			final var successors = new ArrayList<Pair<Territory<P>, P>>();
			boolean subsumed = false;

			for (final var transition : (Iterable<Transition<L, P>>) getEnabledTransitions(territory, lawPlace,
					proofPlaces)::iterator) {
				final var successor = computeSuccessor(territory, lawPlace, transition);
				final var succTerritory = successor.getFirst();
				final var succLawPlace = successor.getSecond();
				mLogger.debug("successor of %s under transitions %s is %s", pair, transition, successor);

				if (lawPlace.equals(succLawPlace) && territory.equals(succTerritory)) {
					// do nothing
					mLogger.debug("\t--> self loop; skipping...");
				} else if (lawPlace.equals(succLawPlace) && subsumes(succTerritory, territory)) {
					subsumed = true;

					// TODO instead of discarding successors for other transitions, should we reuse them?
					// TODO e.g. if size changes, the successor of successor will be the same, no need to discard
					// TODO and maybe in other cases, we can still augment them?
					successors.clear();

					// TODO remember that this transition was already considered; do not consider again for successor
					queue.offer(successor);

					mLogger.debug("\t--> subsumption; abandoning %s...", pair);
					break;
				} else {
					successors.add(successor);
					mLogger.debug("\t--> regular successor; adding...");
				}
			}

			if (!subsumed) {
				result.add(pair);
			}
			for (final var succ : successors) {
				queue.offer(succ);
			}
		}

		return result;
	}

	private Pair<Territory<P>, P> getInitialPair(final Set<P> proofPlaces) {
		final var initialLaw = DataStructureUtils.getOneAndOnly(
				DataStructureUtils.intersection(mRefinedNet.getInitialPlaces(), proofPlaces), "initial law place");
		final var regions = DataStructureUtils.intersection(mRefinedNet.getInitialPlaces(), mOriginalPlaces).stream()
				.map(p -> new Region<>(ImmutableSet.singleton(p))).collect(ImmutableSet.collector());
		return new Pair<>(new Territory<>(regions), initialLaw);
	}

	private boolean enables(final Territory<P> territory, final P lawPlace, final Set<P> proofPlaces,
			final Transition<L, P> transition) {
		// TODO how should we handle transitions where some successor places are not reachable in the refined net
		// (but may well be reachable in the original net?)
		// This can happen because we look at each automaton individually; another automaton not currently considered
		// may be responsible for the non-reachability.

		// mLogger.debug(" checking enabledness of transition %s (pred: %s, succ: %s) under %s and %s", transition,
		// transition.getPredecessors(), transition.getSuccessors(), territory, lawPlace);
		final var regions = new HashSet<>(territory.getRegions());
		for (final var place : transition.getPredecessors()) {
			if (place.equals(lawPlace) || (mAssertionPlaces.contains(place) && !proofPlaces.contains(place))) {
				continue;
			}
			if (proofPlaces.contains(place)) {
				// mLogger.debug(" --> rejected because of predecessor %s", place);
				return false;
			}

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

	private Stream<Transition<L, P>> getEnabledTransitions(final Territory<P> territory, final P lawPlace,
			final Set<P> proofPlaces) {
		final var mayPlaces = DataStructureUtils.union(territory.getPlaces(), Set.of(lawPlace),
				DataStructureUtils.difference(mAssertionPlaces, proofPlaces));
		// mLogger.debug("Computing successors of %s and %s.", territory, lawPlace);
		// mLogger.debug(" may places: %s", mayPlaces);
		// mLogger.debug(" must places: %s", territory.getPlaces());
		return mRefinedNet.getSuccessorTransitionProviders(territory.getPlaces(), mayPlaces).stream()
				.flatMap(provider -> provider.getTransitions().stream())
				.filter(t -> enables(territory, lawPlace, proofPlaces, t));
	}

	private Pair<Territory<P>, P> computeSuccessor(final Territory<P> territory, final P lawPlace,
			final Transition<L, P> transition) {
		// assert enables(territory, lawPlace, transition) : "transition is not enabled, cannot compute successor";

		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		final P newLawPlace =
				predecessors.contains(lawPlace)
						? DataStructureUtils.getOneAndOnly(DataStructureUtils.difference(successors, mOriginalPlaces),
								"law place")
						: lawPlace;

		final var regions = new HashSet<Region<P>>();

		// add bystanders
		for (final var region : territory.getRegions()) {
			if (DataStructureUtils.haveEmptyIntersection(region.getPlaces(), predecessors)) {
				regions.add(region);
			}
		}

		if (predecessors.size() != successors.size() || newLawPlace != lawPlace) {
			for (final var succ : successors) {
				if (mOriginalPlaces.contains(succ)) {
					regions.add(new Region<>(ImmutableSet.singleton(succ)));
				}
			}
		} else {
			final var remainingRegions = new HashSet<>(territory.getRegions());
			for (final var succ : successors) {
				if (!mOriginalPlaces.contains(succ)) {
					continue;
				}
				final var match = findMatchingRegion(remainingRegions, succ, territory);
				if (match == null) {
					regions.add(new Region<>(ImmutableSet.singleton(succ)));
				} else {
					regions.add(
							new Region<>(ImmutableSet.of(DataStructureUtils.union(match.getPlaces(), Set.of(succ)))));
					remainingRegions.remove(match);
				}
			}
		}

		// TODO unify region instances
		// TODO unify Territory instances
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new Pair<>(newTerritory, newLawPlace);
	}

	private boolean subsumes(final Territory<P> subsumer, final Territory<P> subsumee) {
		final var bigRegions = new HashSet<>(subsumer.getRegions());
		for (final var smallRegion : subsumee.getRegions()) {
			final var it = bigRegions.iterator();
			boolean found = false;
			while (it.hasNext()) {
				final var bigRegion = it.next();
				if (bigRegion.getPlaces().containsAll(smallRegion.getPlaces())) {
					it.remove();
					found = true;
					break;
				}
			}
			if (!found) {
				return false;
			}
		}
		return true;
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
}
