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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
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
	// 0: Dominik, 1: Dominik+Elisabeth, 2: Dennis but per-event, 3: Dennis
	private static final int ACCEPTING_TRANSITION_CHECK_STRICTNESS = 2;

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
			final IPostScriptChecker<L, P> postScriptChecker, final BranchingProcess<L, P> completeFinitePrefix,
			final PetriNetRun<L, P> run) {
		super(services, statistics, net, coenabledRelation, run);
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

		final Set<Transition<L, P>> allDeleted = new HashSet<>();
		final Set<P> places = new HashSet<>(net.getPlaces());

		// TODO iteration order nondeterminism
		for (final P pivot : places) {
			if (!isPivotPlace(net, pivot)) {
				continue;
			}

			mLogger.debug("considering pivot place %s", pivot);

			// consider all compositions of incoming and outgoing transitions of pivot
			final var compositions = getCompositionsAt(pivot, net)
					// filter compositions where the labels cannot be composed
					.filter(this::isLabelComposable)
					// filter compositions that cannot be executed due to the net structure
					.filter(c -> isStructurallyComposable(c, net))
					// evaluate compositions and filter those that should not be executed.
					.map(c -> evaluateComposition(c, net)).filter(c -> c != null)
					// collect
					.collect(Collectors.toList());

			// figure out which transitions need to be copied and which need to be deleted
			final var copyAndDelete = classifyTransitions(net, pivot, compositions);
			final var copyTransitions = copyAndDelete.getFirst();
			final var deleteTransitions = copyAndDelete.getSecond();

			final var transition2Copy = copyTransitions(net, pivot, copyTransitions);

			// execute compositions for pivot place
			final var executedCompositions = new ArrayList<ExecutedComposition<L, P>>(compositions.size());
			for (final var comp : compositions) {
				if (!comp.isExecutable()) {
					// This means the transitions t1.t2 can never be fired in direct sequence in a one-safe net:
					// Either some place would need to have 2 tokens, or some place would receive 2 tokens.
					//
					// TODO What is the best course of action here?
					mLogger.debug(" Discarding composition of %s and %s", comp.getFirst(), comp.getSecond());
					continue;
				}

				final var executed = executeComposition(comp);
				executedCompositions.add(executed);
			}

			// delete obsolete transitions
			deleteAll(deleteTransitions);
			allDeleted.addAll(deleteTransitions);

			// adapt run
			if (mRun != null) {
				mRun = adaptRun(mRun, pivot, mPivotCopy, executedCompositions, transition2Copy);
				try {
					assert mRun.isRunOf(net) : "Run adaptation failed";
				} catch (final PetriNetNot1SafeException e) {
					throw new AssertionError("Petri net has become unsafe");
				}
			}

			changes = changes || !executedCompositions.isEmpty() || !copyTransitions.isEmpty()
					|| !deleteTransitions.isEmpty();

			final boolean isYv = net.getPredecessors(pivot).size() != 1;
			LiptonReductionStatisticsDefinitions stat;
			if (executedCompositions.stream().allMatch(EvaluatedComposition::isTrivial)) {
				stat = isYv ? LiptonReductionStatisticsDefinitions.TrivialYvCompositions
						: LiptonReductionStatisticsDefinitions.TrivialSequentialCompositions;
			} else {
				stat = isYv ? LiptonReductionStatisticsDefinitions.ConcurrentYvCompositions
						: LiptonReductionStatisticsDefinitions.ConcurrentSequentialCompositions;
			}
			mStatistics.reportComposition(stat);
		}

		// delete obsolete neighbours of deleted transitions
		deleteObsoleteNeighbours(net, allDeleted);

		// remove unused letters from the alphabet
		pruneAlphabet();

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
			return false;
		}

		return true;
	}

	private Stream<Composition<L, P>> getCompositionsAt(final P pivot, final IPetriNet<L, P> net) {
		return DataStructureUtils.cartesianProduct(net.getPredecessors(pivot), net.getSuccessors(pivot),
				(t1, t2) -> new Composition<>(t1, pivot, t2));
	}

	private Pair<Set<Transition<L, P>>, Set<Transition<L, P>>> classifyTransitions(final IPetriNet<L, P> net,
			final P pivot, final List<EvaluatedComposition<L, P>> compositions) {
		final int numOutgoing = net.getSuccessors(pivot).size();
		final var first2Comp = compositions.stream().collect(Collectors.groupingBy(Composition::getFirst));

		final Set<Transition<L, P>> copyTransitions = new HashSet<>();
		final Set<Transition<L, P>> obsoleteTransitions = new HashSet<>();
		for (final var t1 : net.getPredecessors(pivot)) {
			final var t1Compositions = first2Comp.getOrDefault(t1, Collections.emptyList());
			if (t1Compositions.size() < numOutgoing) {
				// the original transition must be preserved
				mLogger.debug(" keeping first transition " + t1);
			} else if (t1Compositions.stream().anyMatch(c -> isFirstTransitionNeeded(c, net))) {
				// the transition t1 must be copied (with a copy of pivot as successor), the original t1 deleted
				mLogger.debug(" making copy of first transition " + t1);
				copyTransitions.add(t1);
				obsoleteTransitions.add(t1);
			} else {
				// the transition t1 must be deleted
				mLogger.debug("  deleting transition %s without copy", t1);
				obsoleteTransitions.add(t1);
			}
		}

		final int numIncoming = net.getPredecessors(pivot).size();
		final var second2Comp = compositions.stream().collect(Collectors.groupingBy(Composition::getSecond));

		for (final var t2 : net.getSuccessors(pivot)) {
			final var t2Compositions = second2Comp.getOrDefault(t2, Collections.emptyList());
			if (t2Compositions.size() < numIncoming) {
				// the original transition must be preserved
				mLogger.debug(" keeping second transition " + t2);
			} else {
				// the transition t1 must be deleted
				obsoleteTransitions.add(t2);
			}
		}

		return new Pair<>(copyTransitions, obsoleteTransitions);
	}

	// TODO refactor this
	private P mPivotCopy;

	private Map<Transition<L, P>, Transition<L, P>> copyTransitions(final IPetriNet<L, P> net, final P pivot,
			final Collection<Transition<L, P>> transitions) {
		P pivotCopyNonAccepting = null;
		// P pivotCopyAccepting = null;

		final Map<Transition<L, P>, Transition<L, P>> transition2Copy = new HashMap<>();
		for (final Transition<L, P> t : transitions) {
			P pivotCopy;
			// if (hasAcceptingSuccessor(t, petriNet)) {
			// if (pivotCopyAccepting == null) {
			// pivotCopyAccepting = mPlaceFactory.copyPlace(entry.getKey());
			// petriNet.addPlace(pivotCopyAccepting, false, true);
			// }
			// pivotCopy = pivotCopyAccepting;
			// } else {
			if (pivotCopyNonAccepting == null) {
				pivotCopyNonAccepting = mPlaceFactory.copyPlace(pivot);
				addPlace(pivotCopyNonAccepting, false, false);
			}
			pivotCopy = pivotCopyNonAccepting;
			// }

			// TODO Should the transition have those other successors? Not just deadPlace?
			// TODO (if it just has deadPlace, then deadPlace may have to be accepting)
			final Set<P> post = new HashSet<>(t.getSuccessors());
			post.remove(pivot);
			post.add(pivotCopy);
			mPivotCopy = pivotCopy;

			final Transition<L, P> newTransition =
					addTransition(t.getSymbol(), t.getPredecessors(), ImmutableSet.of(post));
			mRetromorphism.copyTransition(t, newTransition);
			mCoenabledRelation.copyRelationships(t, newTransition);

			transition2Copy.put(t, newTransition);
		}

		return transition2Copy;
	}

	private void deleteAll(final Collection<Transition<L, P>> obsolete) {
		for (final var transition : obsolete) {
			removeTransition(transition);
			mCoenabledRelation.removeElement(transition);
			mRetromorphism.deleteTransition(transition);
		}
	}

	private void deleteObsoleteNeighbours(final IPetriNet<L, P> net,
			final Collection<Transition<L, P>> deletedTransitions) {
		deletedTransitions.stream()
				.flatMap(t -> Stream.concat(t.getPredecessors().stream(), t.getSuccessors().stream())).distinct()
				.filter(p -> net.getPredecessors(p).isEmpty() && net.getSuccessors(p).isEmpty()
						&& !net.getInitialPlaces().contains(p))
				.forEach(this::removePlace);
	}

	// *************************************************** EVALUATE ****************************************************

	private EvaluatedComposition<L, P> evaluateComposition(final Composition<L, P> comp, final IPetriNet<L, P> net) {
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

		final boolean isTrivial = mCoenabledRelation.getImage(comp.getFirst()).isEmpty()
				&& mCoenabledRelation.getImage(comp.getSecond()).isEmpty();

		return new EvaluatedComposition<>(comp, compositionType, isTrivial);
	}

	private boolean isLabelComposable(final Composition<L, ?> comp) {
		final boolean result =
				mCompositionFactory.isSequentiallyComposable(comp.getFirstLabel(), comp.getSecondLabel());
		if (!result) {
			mLogger.debug(" The labels of %s and %s cannot be composed", comp.getFirst(), comp.getSecond());
		}
		return result;
	}

	private boolean isStructurallyComposable(final Composition<L, P> comp, final IPetriNet<L, P> petriNet) {
		final var pivot = comp.getPivot();

		final var t1 = comp.getFirst();
		if (t1.getPredecessors().contains(pivot)) {
			// TODO This condition was in report but not in the code. Is it really needed?
			// TODO ^--- actually it was checked in sequenceRule() -- might make sense: it precludes ALL pairs with t1
			mLogger.debug("  cannot compose t1 = %s at pivot place %s because it loops", t1, pivot);
			return false;
		}

		final var t2 = comp.getSecond();
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

		// TODO we should check this before the previous condition, right?
		if (!mPostScriptChecker.mightGetStuck(petriNet, comp.getPivot())) {
			mLogger.debug("  first transition %s is NOT needed because pivot place %s cannot get stuck",
					comp.getFirst(), comp.getPivot());
			return false;
		}

		if (ACCEPTING_TRANSITION_CHECK_STRICTNESS == 0) {
			return Stream
					.concat(mCoenabledRelation.getImage(comp.getFirst()).stream(),
							mCoenabledRelation.getImage(comp.getSecond()).stream())
					.distinct().anyMatch(t -> hasAcceptingSuccessor(t, petriNet));
		}

		if (ACCEPTING_TRANSITION_CHECK_STRICTNESS == 2) {
			return isFirstTransitionNeeded2(comp, petriNet);
		}

		final Set<Transition<L, P>> relevantTransitions = new HashSet<>();
		if (ACCEPTING_TRANSITION_CHECK_STRICTNESS == 1) {
			if (Stream
					.concat(mCoenabledRelation.getImage(comp.getFirst()).stream(),
							mCoenabledRelation.getImage(comp.getSecond()).stream())
					.distinct().anyMatch(t -> hasAcceptingSuccessor(t, petriNet))) {
				return true;
			}
		} else {
			relevantTransitions.addAll(mCoenabledRelation.getImage(comp.getFirst()));
			relevantTransitions.addAll(mCoenabledRelation.getImage(comp.getSecond()));
		}

		// Check whether any transition which either
		// - is co-enabled to t1 or t2, or
		// - is a successor of a successor place of t1 other than the given place
		// is an ancestor of an accepting place.

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

	private boolean isFirstTransitionNeeded2(final Composition<L, P> comp, final IPetriNet<L, P> petriNet) {
		if (Stream
				.concat(mCoenabledRelation.getImage(comp.getFirst()).stream(),
						mCoenabledRelation.getImage(comp.getSecond()).stream())
				.distinct().anyMatch(t -> hasAcceptingSuccessor(t, petriNet))) {
			return true;
		}

		final var events1 = getLastEvents(comp.getFirst()).collect(Collectors.toList());

		// TODO events2 doesn't work right if t2 is a composition -- it need not be the first event on the path!
		final var events2 = getFirstEvents(comp.getSecond()).collect(Collectors.toSet());

		final Set<Event<L, P>> errorEvents =
				petriNet.getAcceptingPlaces().stream().flatMap(p -> petriNet.getPredecessors(p).stream())
						.flatMap(this::getLastEvents).collect(Collectors.toSet());

		for (final var e1 : events1) {

			final Predicate<Event<L, P>> except;
			final var e2Opt = e1.getSuccessorConditions().stream().filter(c -> c.getPlace() == comp.getPivot())
					.flatMap(c -> c.getSuccessorEvents().stream()).filter(e -> events2.contains(e)).findFirst();
			if (e2Opt.isEmpty()) {
				except = (e -> false);
			} else {
				final var e2 = e2Opt.get();
				except = e -> e.getLocalConfiguration().contains(e2);
			}

			final var relevantEvents =
					e1.getSuccessorConditions().stream().flatMap(c -> c.getSuccessorEvents().stream())
							.filter(e -> !e.getTransition().getPredecessors().contains(comp.getPivot()))
							.collect(Collectors.toList());

			for (final var e3 : relevantEvents) {
				for (final var err : errorEvents) {
					if (isAncestorEventExcept(e3, err, except, new HashSet<>())) {
						mLogger.debug("  first transition %s is needed because of error event %s", comp.getFirst(),
								err);
						return true;
					}
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

	private boolean isAncestorEventExcept(final Event<L, P> src, final Event<L, P> tgt,
			final Predicate<Event<L, P>> except, final HashSet<Event<L, P>> cutOffsVisited) {
		if (except.test(tgt) || except.test(src)) {
			return false;
		}

		if (tgt.getLocalConfiguration().contains(src)) {
			return true;
		}

		for (final Event<L, P> mid : tgt.getLocalConfiguration()) {
			for (final Event<L, P> cutoff : mCutOffs.getImage(mid)) {
				final boolean unvisited = cutOffsVisited.add(cutoff);
				if (unvisited && isAncestorEventExcept(src, cutoff, except, cutOffsVisited)) {
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
		return mIndependence.isIndependent(preconditions, t1.getSymbol(), t2.getSymbol()) == Dependence.INDEPENDENT;
	}

	// **************************************************** EXECUTE ****************************************************

	private ExecutedComposition<L, P> executeComposition(final EvaluatedComposition<L, P> comp) {
		mLogger.debug(" Composing %s and %s at pivot place %s", comp.getFirst(), comp.getSecond(), comp.getPivot());

		final var label = mCompositionFactory.composeSequential(comp.getFirstLabel(), comp.getSecondLabel());
		final var transition = addTransition(label, comp.getPredecessors(), comp.getSuccessors());
		final var executed = new ExecutedComposition<>(comp, transition);

		updateCoenabled(executed);
		mRetromorphism.addTransition(transition, Set.of(comp.getFirst()), Set.of(comp.getSecond()));

		return executed;
	}

	private void updateCoenabled(final ExecutedComposition<L, P> composition) {
		final var composed = composition.getComposedTransition();
		mCoenabledRelation.addAllPairs(composed,
				DataStructureUtils.intersection(mCoenabledRelation.getImage(composition.getFirst()),
						mCoenabledRelation.getImage(composition.getSecond())));
		// for (final var t : mCoenabledRelation.getImage(composition.getFirst())) {
		// if (coenabledTest(t, composition.getFirst(), composition.getSecond())) {
		// mCoenabledRelation.addPair(composed, t);
		// }
		// }
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

	// *************************************************** ADAPT RUN ***************************************************

	// TODO This method does not yet account for postscripts / mightGetStuck. How can this be added?
	// TODO Unclear if efficiency is an issue -- if so, can algorithm be made linear using LinkedList and ListIterator?

	private PetriNetRun<L, P> adaptRun(final PetriNetRun<L, P> oldRun, final P pivot, final P pivotCopy,
			final Collection<ExecutedComposition<L, P>> compositions,
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
		return new PetriNetRun<>(markings, word, transitions);
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
		private final boolean mIsTrivial;

		public EvaluatedComposition(final Composition<L, P> pending, final CompositionType compositionType,
				final boolean isTrivial) {
			super(pending.getFirst(), pending.getPivot(), pending.getSecond());
			mCompositionType = compositionType;
			mIsTrivial = isTrivial;
		}

		public CompositionType getCompositionType() {
			return mCompositionType;
		}

		public boolean isTrivial() {
			return mIsTrivial;
		}
	}

	private static final class ExecutedComposition<L, P> extends EvaluatedComposition<L, P> {
		private final Transition<L, P> mComposedTransition;

		public ExecutedComposition(final EvaluatedComposition<L, P> pending,
				final Transition<L, P> composedTransition) {
			super(pending, pending.getCompositionType(), pending.isTrivial());
			mComposedTransition = composedTransition;
		}

		public Transition<L, P> getComposedTransition() {
			return mComposedTransition;
		}
	}
}
