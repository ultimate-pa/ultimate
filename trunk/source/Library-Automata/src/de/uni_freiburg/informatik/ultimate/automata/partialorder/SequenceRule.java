/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SequenceRule<L, P> extends ReductionRule<L, P> {
	private static final boolean LIBERAL_ACCEPTING_TRANSITION_CHECK = true;

	private final ModifiableRetroMorphism<L, P> mRetromorphism;
	private final BranchingProcess<L, P> mBranchingProcess;
	private final HashRelation<Event<L, P>, Event<L, P>> mCutOffs = new HashRelation<>();

	private final IIndependenceRelation<Set<P>, L> mIndependence;
	private final ICompositionFactory<L> mCompositionFactory;
	private final ICopyPlaceFactory<P> mPlaceFactory;
	private final IPostScriptChecker<L, P> mPostScriptChecker;

	public SequenceRule(final AutomataLibraryServices services, final LiptonReductionStatisticsGenerator statistics,
			final BoundedPetriNet<L, P> net, final CoenabledRelation<L, P> coenabledRelation,
			final ModifiableRetroMorphism<L, P> retromorphism, final IIndependenceRelation<Set<P>, L> independence,
			final ICompositionFactory<L> compositionFactory, final ICopyPlaceFactory<P> placeFactory,
			final IIndependenceCache<?, L> independenceCache, final IPostScriptChecker<L, P> postScriptChecker,
			final BranchingProcess<L, P> completeFinitePrefix) {
		super(services, statistics, net, coenabledRelation, independenceCache);
		mRetromorphism = retromorphism;
		mIndependence = independence;
		mCompositionFactory = compositionFactory;
		mPlaceFactory = placeFactory;
		mPostScriptChecker = postScriptChecker;
		mBranchingProcess = completeFinitePrefix;
		mBranchingProcess.getEvents().stream().filter(Event::isCutoffEvent)
				.forEach(e -> mCutOffs.addPair(e.getCompanion(), e));
	}

	@Override
	protected boolean applyInternal(final IPetriNet<L, P> net) {

		mLogger.debug("----------------------");
		mLogger.debug("applying sequence rule");
		mLogger.debug("----------------------");

		boolean changes = false;

		final Set<Transition<L, P>> obsoleteTransitions = new HashSet<>();
		final Set<Transition<L, P>> composedTransitions = new HashSet<>();
		final List<EvaluatedComposition<L, P>> pendingCompositions = new ArrayList<>();
		final Map<P, Set<Transition<L, P>>> transitionsToBeReplaced = new HashMap<>();

		for (final P pivot : net.getPlaces()) {
			if (!isPivotPlace(net, pivot)) {
				continue;
			}

			mLogger.debug("considering pivot place %s", pivot);

			final Set<Transition<L, P>> incomingTransitions = net.getPredecessors(pivot);
			final Set<Transition<L, P>> outgoingTransitions = net.getSuccessors(pivot);

			// 1. cartesian product of incomingTransitions and outgoingTransitions (of type PendingComposition)
			// 2. filter out uncomposable PendingCompositions (label, structural or Lipton)
			// 3. filter out PendingCompositions involving composedTransitions
			// 4. split into executable and non-executable PendingCompositions
			// 5. determine for all incoming and outgoing transitions if they are obsolete
			// -- (i.e. all pairs involving the transition are still pending or non-executable)
			// 6. for all obsolete incoming transitions, determine if we need a copy or not
			// 7. modify the net: delete obsolete, add copies, add pending compositions

			// For transformations that are not Y-V or reverse-Y-V:
			//
			// An incoming transition t1 for which some t2 was composed is deleted, but, if
			// (a) isFirstTransitionNeeded(t1) or
			// (b) not all (t1, t2) were composed or non-executable,
			// we create a new copy p' of p, a new copy of t1 with its successor p replaced by p',
			// and for all t2 not composed (but executable) with t1,
			// we create a copy t2' with its predecessor p replaced by p'.
			//
			// For multiple t1 with the same outgoing set from their p', we can re-use the place p'.
			// Indeed, we don't even (theoretically) need to only apply this for partially composed t1;
			// for not-at-all composed t1 we have p' = p.
			// In practice, we probably want to avoid that overhead.
			//
			// For reverse-Y-V transformations, where the pivot has only one successor,
			// there might exist situations where it's better to have one p' per successor t2 (only one) rather than per
			// predecessor t1. But we might still need copies of the incoming t1 due to isFirstTransitionNeeded.

			final boolean isYv = incomingTransitions.size() != 1;

			final Set<Transition<L, P>> composedHere = new HashSet<>();
			boolean completeComposition = true;

			final Set<Transition<L, P>> replacementNeeded = new HashSet<>();

			for (final Transition<L, P> t1 : incomingTransitions) {
				if (composedTransitions.contains(t1)) {
					completeComposition = false;
					continue;
				}

				for (final Transition<L, P> t2 : outgoingTransitions) {
					if (composedTransitions.contains(t2)) {
						completeComposition = false;
						continue;
					}

					final var composition = new Composition<>(t1, pivot, t2);
					final var evaluated = evaluateComposition(composition, net, !replacementNeeded.contains(t1));
					if (evaluated == null) {
						completeComposition = false;
						continue;
					}

					if (evaluated.isExecutable()) {
						mLogger.debug(" Composing %s and %s at pivot place %s", t1, t2, pivot);
						pendingCompositions.add(evaluated);
					} else {
						// This means the transitions t1.t2 can never be fired in direct sequence in a one-safe net:
						// Either some place would need to have 2 tokens, or some place would receive 2 tokens.
						//
						// TODO What is the best course of action here?
						// TODO As-is, the subsequent modifications (composedHere, replacementNeeded, statistics,
						// obsoleteTransitions) seem dangerous.
						mLogger.debug(" Discarding composition of " + t1 + " and " + t2 + ".");
					}
					composedHere.add(t1);
					composedHere.add(t2);
					changes = true;

					if (evaluated.requiresFirstTransition()) {
						mLogger.debug(" keeping first transition " + t1);
						replacementNeeded.add(t1);
					}

					// t1 (in an n:1 composition) resp. t2 (in a 1:m composition) is definitely obsolete.
					obsoleteTransitions.add(isYv ? t1 : t2);

					LiptonReductionStatisticsDefinitions stat;
					if (mCoenabledRelation.getImage(t1).isEmpty() && mCoenabledRelation.getImage(t2).isEmpty()) {
						stat = isYv ? LiptonReductionStatisticsDefinitions.TrivialYvCompositions
								: LiptonReductionStatisticsDefinitions.TrivialSequentialCompositions;
					} else {
						stat = isYv ? LiptonReductionStatisticsDefinitions.ConcurrentYvCompositions
								: LiptonReductionStatisticsDefinitions.ConcurrentSequentialCompositions;
					}
					mStatistics.reportComposition(stat);
				}
			}

			if (completeComposition) {
				// If the composition is complete, the single outgoing (for n:1 compositions) resp. incoming (for 1:m
				// compositions) transition is also obsolete.
				obsoleteTransitions.addAll(isYv ? outgoingTransitions : incomingTransitions);
			}

			// TODO Why do we delay the addition to "composedTransitions" ?
			composedTransitions.addAll(composedHere);
			if (!replacementNeeded.isEmpty()) {
				transitionsToBeReplaced.put(pivot, replacementNeeded);
			}
		}

		for (final Map.Entry<P, Set<Transition<L, P>>> entry : transitionsToBeReplaced.entrySet()) {
			P deadNonAccepting = null;
			// P deadAccepting = null;

			for (final Transition<L, P> t : entry.getValue()) {
				P deadPlace;
				// if (hasAcceptingSuccessor(t, petriNet)) {
				// if (deadAccepting == null) {
				// deadAccepting = mPlaceFactory.copyPlace(entry.getKey());
				// petriNet.addPlace(deadAccepting, false, true);
				// }
				// deadPlace = deadAccepting;
				// } else {
				if (deadNonAccepting == null) {
					deadNonAccepting = mPlaceFactory.copyPlace(entry.getKey());
					addPlace(deadNonAccepting, false, false);
				}
				deadPlace = deadNonAccepting;
				// }

				// TODO Should the transition have those other successors? Not just deadPlace?
				// TODO (if it just has deadPlace, then deadPlace may have to be accepting)
				final Set<P> post = new HashSet<>(t.getSuccessors());
				post.remove(entry.getKey());
				post.add(deadPlace);

				// TODO Why again do we create this fresh transition rather than keeping the old one?
				final Transition<L, P> newTransition =
						addTransition(t.getSymbol(), t.getPredecessors(), ImmutableSet.of(post));
				mRetromorphism.copyTransition(t, newTransition);
				mCoenabledRelation.copyRelationships(t, newTransition);
			}
		}

		final var executedCompositions = applyModifications(pendingCompositions, obsoleteTransitions);

		// update information for composed transition
		for (final var comp : executedCompositions) {
			updateCoenabled(comp);
			mRetromorphism.addTransition(comp.getComposedTransition(), Set.of(comp.getFirst()),
					Set.of(comp.getSecond()));
			transferMoverProperties(comp.getComposedLabel(), List.of(comp.getFirstLabel(), comp.getSecondLabel()));
		}

		// delete obsolete information
		for (final Transition<L, P> t : obsoleteTransitions) {
			mCoenabledRelation.removeElement(t);
			mRetromorphism.deleteTransition(t);
		}

		final var obsoleteNeighbours = obsoleteTransitions.stream()
				.flatMap(t -> Stream.concat(t.getPredecessors().stream(), t.getSuccessors().stream()))
				.collect(Collectors.toSet());
		for (final var neighbour : obsoleteNeighbours) {
			if (net.getPredecessors(neighbour).isEmpty() && net.getSuccessors(neighbour).isEmpty()) {
				removePlace(neighbour);
			}
		}

		return changes;
	}

	/**
	 * Identifies place at which the sequence rule can be applied.
	 */
	private boolean isPivotPlace(final IPetriNet<L, P> petriNet, final P place) {
		if (petriNet.getInitialPlaces().contains(place) || petriNet.isAccepting(place)) {
			return false;
		}

		final Set<Transition<L, P>> incomingTransitions = petriNet.getPredecessors(place);
		final Set<Transition<L, P>> outgoingTransitions = petriNet.getSuccessors(place);

		if (incomingTransitions.isEmpty() || outgoingTransitions.isEmpty()) {
			return false;
		}

		if (incomingTransitions.size() != 1 && outgoingTransitions.size() != 1) {
			// At the moment we only allow n:1 or 1:m compositions; because for n:m compositions,
			// (1) the number of transitions increases (n*m instead of n+m), and
			// (2) more importantly, it is unclear how to proceed if not all pairs can be composed.
			//
			// Possible future extension: If some incoming (resp. outgoing) transition t can be composed with all
			// outgoing (resp. incoming) transitions, we can perform these compositions and remove transition t.
			//
			// Alternatively, we could allow all n:m compositions and redirect the remaining uncomposed transitions
			// to several different copies of the current place.
			return false;
		}

		return true;
	}

	// *****************************************************************************************************************

	private void updateCoenabled(final ExecutedComposition<L, P> composition) {
		final var composed = composition.getComposedTransition();
		for (final var t : mCoenabledRelation.getImage(composition.getFirst())) {
			if (coenabledTest(t, composition.getFirst(), composition.getSecond())) {
				mCoenabledRelation.addPair(composed, t);
			}
		}
	}

	// Checks a necessary condition for the transition t to be coenabled with the composition of t1 and t2.
	private boolean coenabledTest(final Transition<L, P> t, final Transition<L, P> t1, final Transition<L, P> t2) {
		assert mCoenabledRelation.containsPair(t1, t);
		if (mCoenabledRelation.containsPair(t2, t)) {
			return true;
		}
		return DataStructureUtils.haveNonEmptyIntersection(t.getPredecessors(), t2.getPredecessors())
				&& DataStructureUtils.intersectionStream(t.getPredecessors(), t2.getPredecessors())
						.allMatch(t1.getSuccessors()::contains);
	}

	// *************************************************** EVALUATE ****************************************************

	private EvaluatedComposition<L, P> evaluateComposition(final Composition<L, P> comp, final IPetriNet<L, P> net,
			final boolean evaluateNeedForFirstTransition) {
		if (!isLabelComposable(comp)) {
			mLogger.debug(" The labels of %s and %s cannot be composed", comp.getFirst(), comp.getSecond());
			return null;
		}
		if (!isStructurallyComposable(comp, net)) {
			return null;
		}

		final CompositionType compositionType;
		if (isRightMoverComposition(comp)) {
			compositionType = CompositionType.RIGHT_MOVER;
		} else if (isLeftMoverComposition(comp)) {
			compositionType = CompositionType.LEFT_MOVER;
		} else {
			return null;
		}

		final boolean requiresFirstTransition;
		if (evaluateNeedForFirstTransition) {
			// TODO add setting to forbid compositions where first transition needed
			requiresFirstTransition = isFirstTransitionNeeded(comp, net);
		} else {
			requiresFirstTransition = false;
		}

		return new EvaluatedComposition<>(comp, compositionType, requiresFirstTransition);
	}

	private boolean isLabelComposable(final Composition<L, ?> comp) {
		return mCompositionFactory.isSequentiallyComposable(comp.getFirstLabel(), comp.getSecondLabel());
	}

	private boolean isStructurallyComposable(final Composition<L, P> comp, final IPetriNet<L, P> petriNet) {
		final var t1 = comp.getFirst();
		final var t2 = comp.getSecond();
		final var pivot = comp.getPivot();

		if (t1.getPredecessors().contains(pivot)) {
			// TODO This condition was in report but not in the code. Is it really needed?
			// TODO ^--- actually it was checked in sequenceRule() -- might make sense: it precludes ALL pairs with t1
			mLogger.debug("  cannot compose t1 = %s at pivot place %s because it loops", t1, pivot);
			return false;
		}

		if (t2.getSuccessors().contains(pivot)) {
			mLogger.debug("  cannot compose t2 = %s at pivot place %s because it loops", t2, pivot);
			return false;
		}

		if (!checkForEventsInBetween2(petriNet, t1, t2, pivot)) {
			mLogger.debug("  cannot compose %s and %s at pivot place %s because of events in between", t1, t2, pivot);
			return false;
		}
		return true;
	}

	private boolean checkForEventsInBetween(final IPetriNet<L, P> petriNet, final Transition<L, P> t1,
			final Transition<L, P> t2, final P pivot) {

		// TODO What precisely is the purpose of this method? can we simplify it?

		final Set<Transition<L, P>> transitions = DataStructureUtils.difference(t1.getSuccessors().stream()
				.flatMap(p2 -> petriNet.getSuccessors(p2).stream()).collect(Collectors.toSet()),
				petriNet.getSuccessors(pivot));

		final Set<Event<L, P>> t1Events =
				transitions.stream().flatMap(this::getFirstEvents).collect(Collectors.toSet());
		final Set<Event<L, P>> t2Events = getLastEvents(t2).collect(Collectors.toSet());

		for (final Event<L, P> e1 : t1Events) {
			for (final Event<L, P> e2 : t2Events) {
				if (isAncestorEvent(e1, e2, new HashSet<>())) {
					return false;
				}
			}
		}

		return true;
	}

	// Candidate replacement for checkEventsInBetween.
	//
	// Performs a backwards search from events for transition t2, looking for a path to an event for t1 that contains
	// some event for a predecessor or successor transition of the pivot place (the start and target events excluded).
	//
	// The search does not have to go deep: Either an event is found immediately, or a target is reached. In either
	// case, the search terminates. However, we need special handling for cut-off events.
	//
	// The idea is that if no such path exists, then all events occurring between t1 and t2 in a firing sequence
	// must be co-related with either t1 or t2 (assuming no other predecessor or successor of the pivot place occurs).
	//
	private boolean checkForEventsInBetween2(final IPetriNet<L, P> petriNet, final Transition<L, P> t1,
			final Transition<L, P> t2, final P pivot) {
		final var targets = getLastEvents(t1).collect(Collectors.toSet());

		final var queue = new ArrayDeque<Event<L, P>>();
		final var visited = new HashSet<Event<L, P>>();

		// TODO potential iteration order nondeterminism
		getFirstEvents(t2).flatMap(e2 -> e2.getPredecessorEvents().stream()).forEach(queue::offer);

		while (!queue.isEmpty()) {
			final var ev = queue.poll();

			final var unvisited = visited.add(ev);
			if (!unvisited) {
				continue;
			}

			// Add all cut-off events to the stack that have the current event ev as companion.
			// Such cut-off events result in the same marking as the current event ev,
			// and hence can also result in the execution of an event start' for the same transition as start.
			// Since the event start' is not included in the finite prefix,
			// we simulate backwards search from start' here.
			// TODO potential iteration order nondeterminism
			queue.addAll(mCutOffs.getImage(ev));

			if (targets.stream().noneMatch(ev.getLocalConfiguration()::contains)) {
				// we are not on a path back to a target, so ignore this node
				continue;
			}

			final var trans = ev.getTransition();
			if (trans.getPredecessors().contains(pivot) || trans.getSuccessors().contains(pivot)) {
				// ignore paths through predecessors or successors of the pivot
				continue;
			}

			if (targets.contains(ev)) {
				// the path consists only of a single place, and can be ignored
				continue;
			}

			// the path contains at least event ev; so ev is between start and targets
			return false;
		}
		return true;
	}

	// *****************************************************************************************************************

	/**
	 * Check whether the first transition needs to be kept after composing two transitions.
	 *
	 * @param pivot
	 *            The place where the compositions happens at.
	 * @param t1
	 *            The first transition.
	 * @param t2
	 *            The second transition.
	 * @param petriNet
	 *            The Petri net.
	 * @return true if the first transition is still needed after composition, false if the transition can be deleted.
	 */
	private boolean isFirstTransitionNeeded(final Composition<L, P> comp, final IPetriNet<L, P> petriNet) {
		if (hasAcceptingSuccessor(comp.getFirst(), petriNet)) {
			// If any successor of t1 is accepting, we need to preserve t1.
			mLogger.debug("  first transition %s is needed because it has accepting successors", comp.getFirst());
			return true;
		}

		if (!mPostScriptChecker.mightGetStuck(petriNet, comp.getPivot())) {
			mLogger.debug("  first transition %s is NOT needed because pivot place %s cannot get stuck",
					comp.getFirst(), comp.getPivot());
			return false;
		}

		if (LIBERAL_ACCEPTING_TRANSITION_CHECK) {
			return Stream
					.concat(mCoenabledRelation.getImage(comp.getFirst()).stream(),
							mCoenabledRelation.getImage(comp.getSecond()).stream())
					.distinct().anyMatch(t -> hasAcceptingSuccessor(t, petriNet));
		}

		// Check whether any transition which either
		// - is co-enabled to t1 or t2, or
		// - is a successor of a successor place of t1 other than the given place
		// is an ancestor of an accepting place.
		final Set<Transition<L, P>> relevantTransitions = new HashSet<>(mCoenabledRelation.getImage(comp.getFirst()));
		relevantTransitions.addAll(mCoenabledRelation.getImage(comp.getSecond()));

		// TODO Which version is correct? Or neither? Or something different? (see tests)
		// t1.getSuccessors().stream().filter(p -> p != place).flatMap(p -> petriNet.getSuccessors(p).stream())
		// .forEach(relevantTransitions::add);
		comp.getFirst().getSuccessors().stream().flatMap(p -> petriNet.getSuccessors(p).stream())
				.filter(t -> !petriNet.getSuccessors(comp.getPivot()).contains(t)).forEach(relevantTransitions::add);

		final Set<Event<L, P>> events =
				relevantTransitions.stream().flatMap(this::getFirstEvents).collect(Collectors.toSet());
		final Set<Event<L, P>> errorEvents =
				petriNet.getAcceptingPlaces().stream().flatMap(p -> petriNet.getPredecessors(p).stream())
						.flatMap(this::getLastEvents).collect(Collectors.toSet());

		for (final Event<L, P> errorEvent : errorEvents) {
			for (final Event<L, P> e : events) {
				if (isAncestorEvent(e, errorEvent, new HashSet<>())) {
					mLogger.debug("  first transition %s is needed because of error event %s", comp.getFirst(),
							errorEvent);
					return true;
				}
			}
		}
		return false;
	}

	private boolean hasAcceptingSuccessor(final Transition<L, P> t, final IPetriNet<L, P> petriNet) {
		return t.getSuccessors().stream().anyMatch(petriNet::isAccepting);
	}

	private Stream<Event<L, P>> getFirstEvents(final Transition<L, P> t) {
		return mRetromorphism.getFirstTransitions(t).stream().flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private Stream<Event<L, P>> getLastEvents(final Transition<L, P> t) {
		return mRetromorphism.getLastTransitions(t).stream().flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private boolean isAncestorEvent(final Event<L, P> e1, final Event<L, P> e2, final Set<Event<L, P>> cutOffsVisited) {
		if (e2.getLocalConfiguration().contains(e1)) {
			return true;
		}

		for (final Event<L, P> e3 : e2.getLocalConfiguration()) {
			for (final Event<L, P> cutoff : mCutOffs.getImage(e3)) {
				final boolean unvisited = cutOffsVisited.add(cutoff);
				if (unvisited && isAncestorEvent(e1, cutoff, cutOffsVisited)) {
					return true;
				}
			}
		}

		return false;
	}

	// ************************************************* LIPTON MOVERS *************************************************

	private boolean isRightMoverComposition(final Composition<L, P> comp) {
		final Set<Transition<L, P>> coEnabled1 = mCoenabledRelation.getImage(comp.getFirst());
		final Set<Transition<L, P>> coEnabled2 = mCoenabledRelation.getImage(comp.getSecond());

		if (!coEnabled1.containsAll(coEnabled2)) {
			mLogger.debug(" %s does not have a superset of coenabled transitions compared with %s", comp.getFirst(),
					comp.getSecond());
			return false;
		}

		if (!isRightMover(comp.getFirst(), coEnabled1)) {
			mLogger.debug(" %s is not a right-mover", comp.getFirst());
			return false;
		}

		mLogger.debug(" %s is a right-mover and has a superset of coenabled transitions compared with %s",
				comp.getFirst(), comp.getSecond());
		return true;
	}

	private boolean isRightMover(final Transition<L, P> t1, final Set<Transition<L, P>> coEnabledTransitions) {
		return coEnabledTransitions.stream().allMatch(t -> areIndependent(t1, t));
	}

	private boolean isLeftMoverComposition(final Composition<L, P> comp) {
		final Set<Transition<L, P>> coEnabled1 = mCoenabledRelation.getImage(comp.getFirst());
		final Set<Transition<L, P>> coEnabled2 = mCoenabledRelation.getImage(comp.getSecond());

		if (!coEnabled2.containsAll(coEnabled1)) {
			mLogger.debug(" %s does not have a superset of coenabled transitions compared with %s", comp.getSecond(),
					comp.getFirst());
			return false;
		}

		if (!isLeftMover(comp.getSecond(), coEnabled2)) {
			mLogger.debug(" %s is not a left-mover", comp.getSecond());
			return false;
		}

		mLogger.debug(" %s is a left-mover and has a superset of coenabled transitions compared with %s",
				comp.getSecond(), comp.getFirst());
		return true;
	}

	private boolean isLeftMover(final Transition<L, P> t2, final Set<Transition<L, P>> coEnabledTransitions) {
		return coEnabledTransitions.stream().allMatch(t -> areIndependent(t, t2));
	}

	private boolean areIndependent(final Transition<L, P> t1, final Transition<L, P> t2) {
		final Set<P> preconditions;
		if (mIndependence.isConditional()) {
			preconditions = DataStructureUtils.union(t1.getPredecessors(), t2.getPredecessors());
		} else {
			preconditions = null;
		}
		return mIndependence.contains(preconditions, t1.getSymbol(), t2.getSymbol());
	}

	// **************************************************** EXECUTE ****************************************************

	private List<ExecutedComposition<L, P>> applyModifications(final List<EvaluatedComposition<L, P>> pending,
			final Set<Transition<L, P>> obsoleteTransitions) {
		final var result = new ArrayList<ExecutedComposition<L, P>>();
		for (final var composition : pending) {
			final var executed = executeComposition(composition);
			result.add(executed);
		}
		for (final var obsolete : obsoleteTransitions) {
			removeTransition(obsolete);
		}
		pruneAlphabet();
		return result;
	}

	private ExecutedComposition<L, P> executeComposition(final EvaluatedComposition<L, P> comp) {
		final var label = mCompositionFactory.composeSequential(comp.getFirstLabel(), comp.getSecondLabel());
		final var transition = addTransition(label, comp.getPredecessors(), comp.getSuccessors());
		return new ExecutedComposition<>(comp, transition);
	}

	// *************************************************** ADAPT RUN ***************************************************

	// TODO This method does not yet account for postscripts / mightGetStuck. How can this be added?
	// TODO Unclear if efficiency is an issue -- if so, can algorithm be made linear using LinkedList and ListIterator?

	private PetriNetRun<L, P> adaptRun(final PetriNetRun<L, P> oldRun, final P pivot, final P pivotCopy,
			final Set<ExecutedComposition<L, P>> compositions,
			final Map<Transition<L, P>, Transition<L, P>> oldToCopy) {
		final var map =
				compositions.stream().collect(Collectors.toMap(c -> new Pair<>(c.getFirst(), c.getSecond()), c -> c));

		final List<Marking<P>> markings = new ArrayList<>(oldRun.getStateSequence());
		final List<Transition<L, P>> transitions = IntStream.range(0, oldRun.getLength())
				.mapToObj(oldRun::getTransition).collect(Collectors.toCollection(ArrayList::new));

		int i = 0;
		while (i < transitions.size()) {
			final var transition = transitions.get(i);
			if (!transition.getSuccessors().contains(pivot)) {
				// Transition was definitely not involved in the composition, hence skip and continue traversing.
				i++;
				continue;
			}

			final var optJ = IntStream.range(i + 1, transitions.size())
					.filter(k -> transitions.get(k).getPredecessors().contains(pivot)).findFirst();
			if (optJ.isEmpty()) {
				// no successor of pivot is executed, hence pivot has a token in all future markings
				assert markings.subList(i + 1, markings.size()).stream().allMatch(m -> m.contains(pivot));

				if (!oldToCopy.containsKey(transition)) {
					// transition was not fused, hence there is nothing to do
					// TODO or it could have been fused, but because of postScript / mightGetStuck no copy exists
					i++;
					continue;
				}

				// replace transition by its un-fused copy
				transitions.set(i, oldToCopy.get(transition));

				// replace pivot by pivotCopy in all future markings
				for (int k = i + 1; k < markings.size(); ++k) {
					markings.set(k, replace(markings.get(k), pivot, pivotCopy));
				}

				// no other predecessor of pivot can be executed, otherwise pivot would have 2 tokens
				assert transitions.subList(i + 1, transitions.size()).stream()
						.allMatch(t -> !t.getSuccessors().contains(pivot));
				break;
			}

			final int j = optJ.getAsInt();

			final var secondTransition = transitions.get(j);
			final var composition = map.get(new Pair<>(transition, secondTransition));
			assert composition != null;

			final var composed = composition.getComposedTransition();

			if (composition.getCompositionType() == CompositionType.RIGHT_MOVER) {
				transitions.set(j, composed);
				transitions.remove(i);

				// adjust markings: remove marking at i+1, and for all markings up to j remove successors of t1
				markings.remove(i + 1);
				for (int k = i; k <= j; ++k) {
					markings.set(k, removeAll(markings.get(k), transition.getSuccessors()));
				}
			} else {
				transitions.set(i, composed);
				transitions.remove(j);

				// adjust markings: remove marking j+1, and for all markings up to j add successors of t2
				markings.remove(j + 1);
				for (int k = i + 1; k < j; ++k) {
					markings.set(k, addAll(markings.get(k), secondTransition.getSuccessors()));
				}
			}

			// anything between (old) i and j cannot be a predecessor of pivot, otherwise pivot would have two tokens
			// hence skip ahead to the position after secondTransition (which is j now, because we removed a transition)
			i = j;
		}

		final var word = new Word<>((L[]) transitions.stream().map(Transition::getSymbol).toArray());
		final var run = new PetriNetRun<>(markings, word, transitions);

		// try {
		// assert run.isRunOf(mPetriNet);
		// } catch (final PetriNetNot1SafeException e) {
		// throw new AssertionError("Petri net has become unsafe");
		// }
		return run;
	}

	private Marking<P> replace(final Marking<P> oldMarking, final P oldPlace, final P newPlace) {
		final var newMarking = oldMarking.stream().collect(Collectors.toCollection(HashSet::new));
		final var removed = newMarking.remove(oldPlace);
		assert removed;
		final var added = newMarking.add(newPlace);
		assert added;
		return new Marking<>(ImmutableSet.of(newMarking));
	}

	private Marking<P> removeAll(final Marking<P> oldMarking, final Set<P> oldPlaces) {
		final var newMarking = oldMarking.stream().collect(Collectors.toCollection(HashSet::new));
		newMarking.removeAll(oldPlaces);
		assert oldMarking.size() - newMarking.size() == oldPlaces.size();
		return new Marking<>(ImmutableSet.of(newMarking));
	}

	private Marking<P> addAll(final Marking<P> oldMarking, final Set<P> newPlaces) {
		final var newMarking = oldMarking.stream().collect(Collectors.toCollection(HashSet::new));
		newMarking.addAll(newPlaces);
		assert newMarking.size() - oldMarking.size() == newPlaces.size();
		return new Marking<>(ImmutableSet.of(newMarking));
	}

	// *****************************************************************************************************************

	public enum CompositionType {
		RIGHT_MOVER, LEFT_MOVER
	}

	private static class Composition<L, P> {
		protected final Transition<L, P> mFirst;
		protected final Transition<L, P> mSecond;
		protected final P mPivot;

		public Composition(final Transition<L, P> first, final P pivot, final Transition<L, P> second) {
			mFirst = first;
			mSecond = second;
			mPivot = pivot;
		}

		public boolean isExecutable() {
			final Set<P> firstSucc = mFirst.getSuccessors();
			final Set<P> secondPre = mSecond.getPredecessors();

			return DataStructureUtils.intersectionStream(mFirst.getPredecessors(), secondPre)
					.allMatch(firstSucc::contains)
					&& DataStructureUtils.intersectionStream(firstSucc, mSecond.getSuccessors())
							.allMatch(secondPre::contains);
		}

		public ImmutableSet<P> getPredecessors() {
			return ImmutableSet.of(DataStructureUtils.union(mFirst.getPredecessors(),
					DataStructureUtils.difference(mSecond.getPredecessors(), mFirst.getSuccessors())));
		}

		public ImmutableSet<P> getSuccessors() {
			return ImmutableSet.of(DataStructureUtils.union(mSecond.getSuccessors(),
					DataStructureUtils.difference(mFirst.getSuccessors(), mSecond.getPredecessors())));
		}

		public Transition<L, P> getFirst() {
			return mFirst;
		}

		public L getFirstLabel() {
			return mFirst.getSymbol();
		}

		public Transition<L, P> getSecond() {
			return mSecond;
		}

		public L getSecondLabel() {
			return mSecond.getSymbol();
		}

		public P getPivot() {
			return mPivot;
		}
	}

	private static class EvaluatedComposition<L, P> extends Composition<L, P> {
		private final CompositionType mCompositionType;
		private final boolean mRequiresFirstTransition;

		public EvaluatedComposition(final Composition<L, P> pending, final CompositionType compositionType,
				final boolean requiresFirstTransition) {
			super(pending.getFirst(), pending.getPivot(), pending.getSecond());
			mCompositionType = compositionType;
			mRequiresFirstTransition = requiresFirstTransition;
		}

		public CompositionType getCompositionType() {
			return mCompositionType;
		}

		public boolean requiresFirstTransition() {
			return mRequiresFirstTransition;
		}
	}

	private static final class ExecutedComposition<L, P> extends EvaluatedComposition<L, P> {
		private final Transition<L, P> mComposedTransition;

		public ExecutedComposition(final EvaluatedComposition<L, P> pending,
				final Transition<L, P> composedTransition) {
			super(pending, pending.getCompositionType(), pending.requiresFirstTransition());
			mComposedTransition = composedTransition;
		}

		public L getComposedLabel() {
			return mComposedTransition.getSymbol();
		}

		public Transition<L, P> getComposedTransition() {
			return mComposedTransition;
		}
	}
}
