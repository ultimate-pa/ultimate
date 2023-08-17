/*
 * Copyright (C) 2023 Veronika Klasen
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.DfsBookkeeping;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of the sleep set automaton using dynamically computed stratified independence relations. Its basically
 * a depth first traversal over the reduction automaton, during which the automaton is being built.
 *
 *
 * @param <L>
 *            The type of letters of the input automaton. VariableAbstraction says that they need to be IActions?
 * @param <S>
 *            The type of states of the input automaton.
 *
 *
 *            - gibt an, welche übergänge da sind - gibt an, welches abstraktionslevel deren target states haben?
 *
 *            instead of constructing a new automaton modify the input automaton?
 *
 *            possible outcomes: 1) find accepting state -> example trace for next refinement round 2) fully
 *            traverse/build automaton without constructing an accepting state -> program is correct
 *
 *            what do we need to return in those cases?
 */

public class DynamicStratifiedReduction<L, S, R, H extends Set<P>, P> {
	private static final String ABORT_MSG = "visitor aborted traversal";

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOriginalAutomaton;
	private final NestedWordAutomaton<L, R> mReductionAutomaton;
	private final IStratifiedStateFactory<L, S, R, AbstractionLevel<H>> mStateFactory;
	private final ILattice<H> mAbstractionLattice;
	private final R mStartState;
	private final IIndependenceInducedByAbstraction<S, L> mIndependenceProvider;
	private final IProofManager<L, S, H> mProofManager;

	private final IDfsOrder<L, S> mOrder;
	private final IDfsVisitor<L, R> mVisitor;

	private final Deque<Pair<R, OutgoingInternalTransition<L, R>>> mWorklist = new ArrayDeque<>();
	private final DfsBookkeeping<R> mDfs = new DfsBookkeeping<>();
	private final HashMap<S, R> mAlreadyReduced = new HashMap<>();

	private int mIndentLevel = -1;

	/**
	 * Performs a depth-first traversal over the reduction automaton while constructing it. This constructor is called
	 * purely for its side-effects. (We could also return the finished reduction automaton?)
	 *
	 * @param services
	 *            automata services used for logging and timeout management
	 * @param originalAutomaton
	 *            The automaton to be traversed
	 * @param order
	 *            The order in which transitions for each state should be explored
	 * @param visitor
	 *            A visitor to traverse the automaton
	 * @param startingState
	 *            startingState of the original automaton
	 * @param independence
	 *            provides independence relations for the reduction automaton
	 * @throws AutomataOperationCanceledException
	 *             in case of timeout or cancellation
	 */
	public DynamicStratifiedReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> originalAutomaton, final IDfsOrder<L, S> order,
			final IStratifiedStateFactory<L, S, R, AbstractionLevel<H>> stateFactory, final IDfsVisitor<L, R> visitor,
			final S startingState, final ILattice<H> lattice, final IIndependenceInducedByAbstraction<S, L> independence,
			final IProofManager<L, S, H> manager) throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(originalAutomaton) : "Finite automata only";

		mServices = services;
		mLogger = services.getLoggingService().getLogger(DynamicStratifiedReduction.class);
		mAbstractionLattice = lattice;
		mStateFactory = stateFactory;
		mOriginalAutomaton = originalAutomaton;
		mReductionAutomaton = new NestedWordAutomaton<>(services, mOriginalAutomaton.getVpAlphabet(), mStateFactory);
		mStartState = mStateFactory.createStratifiedState(startingState, ImmutableSet.empty(),
				new AbstractionLevel(emptyset, mAbstractionLattice, false), new AbstractionLevel(emptyset, mAbstractionLattice, false);

		mOrder = order;
		mIndependenceProvider = independence;
		mVisitor = visitor;
		mProofManager = manager;

		traverse();
	}

	/**
	 * builds and traverses the reduction automaton
	 *
	 *
	 *
	 * @throws AutomataOperationCanceledException
	 */

	private void traverse() throws AutomataOperationCanceledException {
		// add initial state to reduction automaton
		mReductionAutomaton.addState(true, mOriginalAutomaton.isFinal(mStateFactory.getOriginalState(mStartState)),
				mStartState);
		createSuccessors(mStartState);

		final boolean abortImmediately = visitState(mStartState);
		if (abortImmediately) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		while (!mWorklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final var current = mWorklist.pop();
			final R currentState = current.getFirst();

			// Backtrack states still on the stack whose exploration has finished.
			final boolean abort = backtrackUntil(currentState);
			if (abort) {
				mLogger.debug(ABORT_MSG);
				return;
			}

			final OutgoingInternalTransition<L, R> currentTransition = current.getSecond();
			final R nextState = currentTransition.getSucc();
			debugIndent("Now exploring transition %s --> %s (label: %s)", currentState, nextState,
					currentTransition.getLetter());
			final boolean prune = mVisitor.discoverTransition(currentState, currentTransition.getLetter(), nextState);
			if (mVisitor.isFinished()) {
				mLogger.debug(ABORT_MSG);
				return;
			}

			final int stackIndex;
			if (prune) {
				debugIndent("-> visitor pruned transition");
			} else if (!mDfs.isVisited(nextState)) {
				createSuccessors(nextState);
				final boolean abortNow = visitState(nextState);
				if (abortNow) {
					mLogger.debug(ABORT_MSG);
					return;
				}
			} else if ((stackIndex = mDfs.stackIndexOf(nextState)) != -1) {
				debugIndent("-> state is on stack -- do not unroll loop");
				mDfs.updateLoopHead(currentState, new Pair<>(stackIndex, nextState));
			} else {
				debugIndent("-> state was visited before -- no re-exploration");
				mDfs.backPropagateLoopHead(currentState, nextState);
			}
		}

		final boolean abort = backtrackUntil(mStartState);
		if (abort) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		backtrack();
		mLogger.debug("traversal completed");
	}

	private boolean backtrackUntil(final R state) {
		while (!mDfs.peek().equals(state)) {
			final boolean abort = backtrack();
			if (abort) {
				return true;
			}
		}
		return false;
	}

	// TODO: Add abstraction levels of fully explored states to their predecessor's abstraction level

	private boolean backtrack() {
		final R oldState = mDfs.peek();
		final boolean isComplete = mDfs.backtrack();

		debugIndent("backtracking state %s (complete: %s)", oldState, isComplete);
		mIndentLevel--;
		// give its Abstractionlevel to its parents?
		mVisitor.backtrackState(oldState, isComplete);
		return mVisitor.isFinished();
	}

	// need to create state's outgoing transitions and successors before this
	// check if its a proven state, if so update abstraction level
	private boolean visitState(final R state) {
		assert !mDfs.isVisited(state) : "must never re-visit state";
		mIndentLevel++;
		debugIndent("visiting state %s", state);

		final var originalState = mStateFactory.getOriginalState(state);
		final boolean isProvenState = mProofManager.isProvenState(originalState);
		if (isProvenState) {
			final Set<L> freeVars = mProofManager.getVariables(mProofManager.choseRespProof(originalState));
			mStateFactory.addToAbstractionLevel(state, freeVars);
			// Can one modify states/transitions of the NWA?
		}

		final boolean pruneSuccessors;
		if (mStartState.equals(state)) {
			debugIndent("-> state is start state");
			assert !mDfs.hasStarted() : "start state should be first visited state";
			pruneSuccessors = mVisitor.addStartState(state);
		} else {
			assert mDfs.hasStarted() : "first visited state should be start state";
			pruneSuccessors = mVisitor.discoverState(state);
		}
		if (mVisitor.isFinished()) {
			return true;
		}
		mDfs.push(state);

		if (pruneSuccessors) {
			debugIndent("-> visitor pruned all outgoing edges");
		} else {
			final Comparator<OutgoingInternalTransition<L, R>> comp =
					Comparator.<OutgoingInternalTransition<L, R>, L> comparing(OutgoingInternalTransition::getLetter,
							mOrder.getOrder(mStateFactory.getOriginalState(state))).reversed();
			StreamSupport.stream(mReductionAutomaton.internalSuccessors(state).spliterator(), false).sorted(comp)
					.forEachOrdered(out -> mWorklist.push(new Pair<>(state, out)));
		}
		return false;
	}

	private void debugIndent(final String msg, final Object... params) {
		mLogger.debug("  ".repeat(mIndentLevel) + msg, params);
	}

	// --------------------------------------------------- Stuff for reductionbuilding
	// -----------------------------------------------------------------------------------------

	/**
	 * get original successor states & transitions and add their reduction states/transitions to the reduction automaton
	 * and put them on the Worklist
	 *
	 * @param state
	 *            state whose successors are created
	 */

	private void createSuccessors(final R state) {
		final S originalState = mStateFactory.getOriginalState(state);

		final ImmutableSet<L> toPrune = mStateFactory.getSleepSet(state);
		final Iterator<L> outgoingLetters = mOriginalAutomaton.lettersInternal(originalState).iterator();
		while (outgoingLetters.hasNext()) {
			final L letter = outgoingLetters.next();
			final S originalSucc =
					mOriginalAutomaton.internalSuccessors(originalState, letter).iterator().next().getSucc();
			if (!toPrune.contains(letter)) {
				final R correspRstate = mAlreadyReduced.get(originalState);
				/*
				 * If there is no reduction state corresponding to this state of the original automaton or its
				 * corresponding reduction state is in the already completed part of the reduction automaton and
				 * therefore has a higher abstraction level than our current state we create a new reduction state.
				 */
				R reductionSucc;
				if (correspRstate != null | mStateFactory.getAbstractionLevel(correspRstate).isLocked()) {
					final ImmutableSet<L> nextSleepSet = createSleepSet(state, letter);
					reductionSucc = createNextState(state, nextSleepSet, originalSucc, letter);
					mReductionAutomaton.addState(mOriginalAutomaton.isInitial(originalSucc),
							mOriginalAutomaton.isFinal(originalSucc), reductionSucc);
					mReductionAutomaton.addInternalTransition(state, letter, reductionSucc);
					mAlreadyReduced.remove(originalSucc); // old reduction state will be replaced by its copy
					mAlreadyReduced.put(originalSucc, reductionSucc);
				}
				/*
				 * If we are inside a loop we first check if the loop edge from our current state to the existing
				 * reduction state is legal. If so we simply add it to the reduction automaton, if not we start building
				 * a loop copy.
				 */

				else if (((!mStateFactory.isLoopCopy(state))
						& mStateFactory.getLoopablePredecs(state).contains(correspRstate))
						| (mStateFactory.isLoopCopy(state) & (mStateFactory.getAbstractionLevel(state)
								.getValue() == mStateFactory.getAbstractionLimit(correspRstate).getValue()))) {
					// if the abstraction level of the corresp. red. state is not yet defined it is still on the stack
					// -> we're in a loop
					mReductionAutomaton.addInternalTransition(state, letter, correspRstate);
					reductionSucc = correspRstate;
				} else {
					// create a copystate with fixed abstractionlimit for its subgraph
					final ImmutableSet<L> nextSleepSet = createSleepSet(state, letter);
					final AbstractionLevel<L> nextAbstractionLimit =
							new AbstractionLevel(mStateFactory.getAbstractionLevel(state).getValue(), true);
					final AbstractionLevel<L> nextAbstractionLevel =
							new AbstractionLevel(nextAbstractionLimit.getValue(), true);
					reductionSucc = mStateFactory.createStratifiedState(originalState, nextSleepSet,
							nextAbstractionLevel, nextAbstractionLimit, new LinkedList<>());
					mReductionAutomaton.addState(mOriginalAutomaton.isInitial(originalSucc),
							mOriginalAutomaton.isFinal(originalSucc), reductionSucc);
					mReductionAutomaton.addInternalTransition(state, letter, reductionSucc);
					mAlreadyReduced.remove(originalSucc); // old reduction state will be replaced by its copy
					mAlreadyReduced.put(originalSucc, reductionSucc);
				}
				// add state + new reduced transition to worklist
				mWorklist.add(new Pair(state, new OutgoingInternalTransition(letter, reductionSucc)));
			}
		}
	}

	/*
	 * * create the sleep set for a state of the reduction automaton
	 *
	 * @param current The current state of the reduction automaton
	 *
	 * @param letter The letter on the transition from the current state to the state whose sleepset is being created
	 */
	private ImmutableSet<L> createSleepSet(final R current, final L letter) {

		final S currentS = mStateFactory.getOriginalState(current);
		final ImmutableSet<L> currSleepSet = mStateFactory.getSleepSet(current);
		final IIndependenceRelation<S, L> Independence =
				mIndependenceProvider.getInducedIndependence(mStateFactory.getAbstractionLevel(current).getValue());

		// stolen from minimal sleep set reduction

		final Comparator<L> comp = mOrder.getOrder(currentS);
		final Stream<L> explored = mOriginalAutomaton.lettersInternal(currentS).stream()
				.filter(x -> comp.compare(x, letter) < 0 && !currSleepSet.contains(x));

		// TODO: check if this is ok

		final HashSet<L> protVar = (HashSet<L>) Set.of(Stream.concat(currSleepSet.stream(), explored)
				.filter(l -> Independence.isIndependent(currentS, letter, l) == Dependence.INDEPENDENT).toArray());
		final ImmutableSet<L> sleepSet = ImmutableSet.of((Set<L>) Set.of(Stream.concat(currSleepSet.stream(), explored)
				.filter(l -> Independence.isIndependent(currentS, letter, l) == Dependence.INDEPENDENT).toArray()));

		return sleepSet;
	}

	/**
	 * Create a newly discovered state of the reduction automaton
	 *
	 *
	 * @param predecState
	 *            State of the reduction automaton from which the new state was discovered
	 * @param sleepSet
	 *            Sleep set of the new state
	 * @param originState
	 *            State of the original automaton that corresponds to the new state
	 * @param letter
	 *            Letter of the transition leading to the new state
	 *
	 * @return The reduction state
	 */

	private R createNextState(final R predecState, final ImmutableSet<L> sleepSet, final S originState,
			final L letter) {

		final LinkedList<R> loopablepredecs = new LinkedList<>();

		// If the current transition is the smallest (unpruned) outgoing transition of the state let it 'inherit' the
		// list of loopable predecessors

		final Stream<L> smallerEdges = mOriginalAutomaton.lettersInternal(originState).stream()
				.filter(x -> mOrder.getOrder(originState).compare(x, letter) < 0
						&& !mStateFactory.getSleepSet(predecState).contains(x));
		if (smallerEdges.findAny().isEmpty()) {
			loopablepredecs.addAll(mStateFactory.getLoopablePredecs(predecState));
			loopablepredecs.add(predecState);
		}

		// Abstraction limit of the new state is the abstraction limit of its parent + the abstraction levels of the
		// edges in its sleepset
		final HashSet<L> protectedVars = mStateFactory.getAbstractionLimit(predecState).getValue();
		final Iterator<L> comEdges = sleepSet.iterator();
		while (comEdges.hasNext()) {
			final R succState =
					mReductionAutomaton.internalSuccessors(predecState, comEdges.next()).iterator().next().getSucc();
			protectedVars.addAll(mStateFactory.getAbstractionLevel(succState).getValue());
		}

		return mStateFactory.createStratifiedState(originState, sleepSet,
				new AbstractionLevel<>(protectedVars, mStateFactory.getAbstractionLimit(predecState).isLocked()),
				new AbstractionLevel<>(protectedVars, false), loopablepredecs);
	}
}
