/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 * Copyright (C) 2025 LMU Munich
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.AStarHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.IHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopExitAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.UnknownState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Get an accepting run of a nested word automaton. Based on IsEmpty but adapted for Parallel CEGAR Loop.
 *
 * The idea is to have a preprocessing that finds a path (prefix) to an arbitrary state not taken by any other
 * counterexample. Then we call BFS in this arbitrary state to find a path (suffix) to a goal state. At the end both
 * paths are merged.
 *
 * This class uses recursion. It recursively explores the successor of a state. TODO: non recursive
 *
 * Non-terminating if every existing counterexample is in the @mActiveCounterexamples set but the state space is
 * infinite.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class IsEmptyParallel<LETTER, STATE> extends IsEmpty<LETTER, STATE> {

	private final Map<STATE, List<STATE>> mVisitedCallPairs = new HashMap<>();
	private long mStart = 0;
	private long mTimeSpendSearching = 0;
	private final long mTimeOut;
	private int mCountRecursionSteps = 0; // To prevent stack overflows
	private int countFailedRunConstruction = 0;
	private boolean mTimedout = false;
	private int mLoopBound = -1;
	// a -> b then state is a
	private final List<Pair<STATE, LETTER>> mCurrentPrefix = new ArrayList<>();

	/**
	 * HashMap used for parallel trace abstraction Maps TraceHash to Trace, has an entry for every counterexample
	 * currently checked by a thread
	 */
	private final HashMap<Integer, NestedRun<LETTER, ?>> mActiveCounterexamples;

	/**
	 * Constructor for parallel search strategy. Gets as additional argument the list of all counterexamples currently
	 * investigated. Tries to find a new counterexample as much different as possible from the once considered.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @param strategy
	 *            search strategy
	 */
	public IsEmptyParallel(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final Set<STATE> startStates,
			final Set<STATE> forbiddenStates, final Set<STATE> goalStates, final boolean goalStateIsAcceptingState,
			final SearchStrategy strategy, final HashMap<Integer, NestedRun<LETTER, ?>> counterexamples,
			final int loopBound) throws AutomataOperationCanceledException {
		super(services, operand, startStates, forbiddenStates, goalStates, goalStateIsAcceptingState, strategy, true);

		// BFS or DFS for search when we call IsEmpty at the end of parallel search
		assert mStrategy.equals(SearchStrategy.BFS);
		mLoopBound = loopBound;

		// In case the search is non terminating
		mStart = System.nanoTime() / 1000000000;
		mTimeOut = mStart + 50000; // 5 sec timeout atm

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		mActiveCounterexamples = counterexamples;

		mAcceptingRun = getAcceptingRunParallel(mActiveCounterexamples.keySet());

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * Mark a call state pair a visited. Only used for tracking the caller of a call not for the bfs search
	 */
	private void markCallVisited(final STATE state, final STATE stateK) {
		List<STATE> callPreds = mVisitedCallPairs.get(state);
		if (callPreds == null) {
			callPreds = new ArrayList<>();
			mVisitedCallPairs.put(state, callPreds);
		}
		// TODO evaluate if using a List instead of a Set for callPreds solves our recusrion issues
//		if (callPreds.contains(stateK)) {
//			System.out.println(stateK);
//		}
//		assert !callPreds.contains(stateK);
		callPreds.add(stateK);
	}

	// unmark incase we backtrack or explore a return
	private void unmarkCall(final STATE state, final STATE stateK) {
		final List<STATE> callPreds = mVisitedCallPairs.get(state);
		assert callPreds != null : "Call was not visited! " + state + " " + stateK;
		callPreds.remove(stateK);
	}

	@Override
	protected void getAcceptingRunHelperReturn(final STATE state, final STATE stateK) {
		for (final OutgoingReturnTransition<LETTER, STATE> transition : mOperand.returnSuccessorsGivenHier(state,
				stateK)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mForbiddenStates.contains(succ)) {
				continue;
			}
			for (final STATE stateKk : getCallStatesOfCallState(stateK)) {
				if (!wasVisited(succ, stateKk)) {
					unmarkCall(stateK, stateKk);
					enqueueAndMarkVisited(succ, stateKk);
					addRunInformationReturn(succ, stateKk, symbol, state, stateK);
				}
			}
		}
	}

	@Override
	protected Set<STATE> getCallStatesOfCallState(final STATE callState) {
		Set<STATE> callStatesOfCallStates = mVisitedPairs.get(callState);
		if (callStatesOfCallStates == null) {
			callStatesOfCallStates = new HashSet<>(mVisitedCallPairs.get(callState));
			if (callStatesOfCallStates == null) {
				return Collections.emptySet();
			}
		}
		return callStatesOfCallStates;
	}

	private PQState getSuccFromSummary(final Entry<STATE, STATE> entry, final int position, final STATE state,
			final ArrayList<Integer> counterexamples) {
		final Map<STATE, LETTER> succ2ReturnSymbol = mSummaryReturnSymbol.get(state);
		final ArrayList<Integer> activeCounterexamples = new ArrayList<>();
		final STATE succ = entry.getKey();
		if (!succ2ReturnSymbol.containsKey(succ)) {
			throw new AssertionError("Getting Summary failed!");
		}
		final STATE returnPred = entry.getValue();
		final LETTER symbol = succ2ReturnSymbol.get(succ);
		int currentScore = 0;
		for (final int cexHash : counterexamples) {
			final NestedRun<LETTER, ?> counterexample = mActiveCounterexamples.get(cexHash);
			if (counterexample.getLength() > position) {
				IcfgLocation programPoint = null;
				final STATE stateInCEx = (STATE) counterexample.getStateAtPosition(position);
				if (stateInCEx instanceof Return || succ instanceof Return) {
					if (symbol == counterexample.getSymbol(position - 1)) {
						currentScore += 1;
						activeCounterexamples.add(cexHash);
					}
				} else if (stateInCEx instanceof ISLPredicate && succ instanceof ISLPredicate) {
					programPoint = ((ISLPredicate) stateInCEx).getProgramPoint();
					if (programPoint.equals(((ISLPredicate) succ).getProgramPoint())) {
						if (symbol == counterexample.getSymbol(position - 1)) {
							currentScore += 1;
							activeCounterexamples.add(cexHash);
						}
					} else {
						if (!(succ instanceof UnknownState
								|| !counterexample.getStateAtPosition(position).equals(succ))) {
							throw new AssertionError("unexpected state in counterexample");
						}
					}
				} else {
					throw new AssertionError("unexpected state in counterexample");
				}

			}
		}
		return new PQState(currentScore, returnPred, symbol, succ, state, activeCounterexamples, false, true);
	}

	private boolean increaseScore(final NestedRun<LETTER, ?> counterexample, final STATE state, final STATE succ,
			final LETTER symbol, final int position) {
		final boolean stateBasedScore = false;
		if (stateBasedScore) {
			return increaseScoreBasedOnStates(counterexample, succ);
		}
		return increaseScoreDefault(counterexample, state, succ, symbol, position);
	}

	/**
	 * increases the score only if a previous counterexample took this edge * AND @position is equal to the position of
	 * the @succ in the counterexample (Prefixes match)
	 *
	 * @param succ
	 */
	private boolean increaseScoreDefault(final NestedRun<LETTER, ?> counterexample, final STATE state, final STATE succ,
			final LETTER symbol, final int position) {
		if (counterexample.getLength() > position) {
			IcfgLocation programPoint = null;
			final STATE stateInCEx = (STATE) counterexample.getStateAtPosition(position);
			if (stateInCEx instanceof ISLPredicate) {
				programPoint = ((ISLPredicate) stateInCEx).getProgramPoint();
			} else {
				throw new AssertionError("Unexpected Predicate");
			}
			// can have different serial numbers! is that a problem?
			if (programPoint.equals(((ISLPredicate) succ).getProgramPoint())
					&& (symbol == counterexample.getSymbol(position - 1))) {
				return true;
			}
		}
		return false;
	}

	/*
	 * We are less strict here and increase already if the succ occurs in the counterexample no matter the position
	 * Doesnt seem to pay of in our evaluation.
	 */
	private boolean increaseScoreBasedOnStates(final NestedRun<LETTER, ?> counterexample, final STATE succ) {

		final Set<?> stateSet = new HashSet<>(counterexample.getStateSequence());
		if (stateSet.contains(succ)) {
			return true;
		}
		return false;
	}

	// Calculates the score of an internal successor and tracks how many counterexamples in the given set take this
	// successor
	private PQState getSuccOfInternal(final OutgoingInternalTransition<LETTER, STATE> transition, final int position,
			final STATE state, final STATE stateK, final ArrayList<Integer> counterexamples) {
		final LETTER symbol = transition.getLetter();
		final STATE succ = transition.getSucc();
		final ArrayList<Integer> activeCounterexamples = new ArrayList<>();
		int currentScore = 0;
		for (final int cexHash : counterexamples) {
			final NestedRun<LETTER, ?> counterexample = mActiveCounterexamples.get(cexHash);
			if (increaseScore(counterexample, state, succ, symbol, position)) {
				currentScore += 1;
				activeCounterexamples.add(cexHash);
			}
		}
		return new PQState(currentScore, state, symbol, transition.getSucc(), stateK, activeCounterexamples, false,
				false);
	}

	private PQState getSuccOfCall(final OutgoingCallTransition<LETTER, STATE> transition, final int position,
			final STATE state, final STATE stateK, final ArrayList<Integer> counterexamples) {
		final LETTER symbol = transition.getLetter();
		final STATE succ = transition.getSucc();
		final ArrayList<Integer> activeCounterexamples = new ArrayList<>();
		int currentScore = 0;
		for (final int cexHash : counterexamples) {
			final NestedRun<LETTER, ?> counterexample = mActiveCounterexamples.get(cexHash);
			if (increaseScore(counterexample, state, succ, symbol, position)) {
				currentScore += 1;
				activeCounterexamples.add(cexHash);
			}
		}
		return new PQState(currentScore, state, symbol, transition.getSucc(), stateK, activeCounterexamples, true,
				false);
	}

	private PQState getSuccOfReturn(final OutgoingReturnTransition<LETTER, STATE> transition, final int position,
			final STATE state, final STATE stateKk, final ArrayList<Integer> counterexamples) {
		final LETTER symbol = transition.getLetter();
		final STATE succ = transition.getSucc();
		final ArrayList<Integer> activeCounterexamples = new ArrayList<>();
		int currentScore = 0;
		for (final int cexHash : counterexamples) {
			final NestedRun<LETTER, ?> counterexample = mActiveCounterexamples.get(cexHash);
			if (increaseScore(counterexample, state, succ, symbol, position)) {
				currentScore += 1;
				activeCounterexamples.add(cexHash);
			}
		}
		return new PQState(currentScore, state, symbol, transition.getSucc(), stateKk, activeCounterexamples, false,
				true);
	}

	// This can be used to restrict the search to omit exploring certain successors, e.g., loop entry locations
	private boolean exploreThisSuccessor(final STATE state, final LETTER letter, final STATE succ) {
		if (mForbiddenStates.contains(succ)) {
			return false;
		}
		if (atLoopBound(state, letter)) {
			return false;
		}
		return true;
	}

	private boolean atLoopBound(final STATE state, final LETTER letter) {
		if (mLoopBound == -1) {
			return false;
		}
		if (isLoopEntryLocation(state) && entersLoopBody(letter)) {
			int countLetters = 0; // amount of loop unrollings
			int countStates = 0; // amount of new loop unrollings
			for (final Pair<STATE, LETTER> transition : mCurrentPrefix) {
				if (transition.getSecond().equals(letter)) {
					countLetters += 1;
				}
				// letter can be the same but state different
				// Then its an unknownstate and the loop was already unrolled
				if (transition.getFirst().equals(state)) {
					countStates += 1;
				}
			}
			if (countLetters >= mLoopBound && countStates > 1) { // we see it once when exiting the loop
				return true;
			}
		}
		return false;

	}

	private boolean entersLoopBody(final LETTER letter) {
		final CodeBlock stmt = ((CodeBlock) letter);
		if (stmt.getPayload().getAnnotations().containsKey(LoopExitAnnotation.class.getName())) {
			return false;
		}
		return true;
	}

	private boolean isLoopEntryLocation(final STATE state) {
		final IcfgLocation a = ((ISLPredicate) state).getProgramPoint();
		if (a.getPayload().getAnnotations().containsKey(LoopEntryAnnotation.class.getName())) {
			return true;
		}
		return false;
	}

	/**
	 * Sort the outgoing transitions by how many @param counterexamples cover them. The least has highest priority.
	 */
	private PriorityQueue<PQState> pickSuccToExplore(final int position, final STATE state, final STATE stateK,
			final ArrayList<Integer> counterexamples) {
		final PriorityQueue<PQState> pq = new PriorityQueue<>(Comparator.comparingInt(PQState::getScore));

		if (mSummaryReturnPred.containsKey(state)) {
			if (!mSummaryReturnSymbol.containsKey(state)) {
				throw new AssertionError("Summary Failed");
			}
			final Map<STATE, STATE> succ2ReturnPred = mSummaryReturnPred.get(state);
			for (final Entry<STATE, STATE> entry : succ2ReturnPred.entrySet()) {
				pq.add(getSuccFromSummary(entry, position, state, counterexamples));
			}
			// after we process a summary we must not process the return anymore!!
			return pq;
		}

		boolean firstIteration = true;
		final Iterator<OutgoingInternalTransition<LETTER, STATE>> internalIterator =
				mOperand.internalSuccessors(state).iterator();
		while (internalIterator.hasNext()) {
			final OutgoingInternalTransition<LETTER, STATE> transition = internalIterator.next();
			final STATE succ = transition.getSucc();
			if (!exploreThisSuccessor(state, transition.getLetter(), succ)) {
				continue;
			}
			if (firstIteration && !internalIterator.hasNext()) {
				pq.add(new PQState(1, state, transition.getLetter(), transition.getSucc(), stateK, counterexamples,
						false, false));
			} else {
				pq.add(getSuccOfInternal(transition, position, state, stateK, counterexamples));
			}
			firstIteration = false;
		}

		final Iterator<OutgoingCallTransition<LETTER, STATE>> callIterator = mOperand.callSuccessors(state).iterator();
		while (callIterator.hasNext()) {
			final OutgoingCallTransition<LETTER, STATE> transition = callIterator.next();
			final STATE succ = transition.getSucc();
			if (!exploreThisSuccessor(state, transition.getLetter(), succ)) {
				continue;
			}
			if (firstIteration && !callIterator.hasNext()) {
				pq.add(new PQState(1, state, transition.getLetter(), transition.getSucc(), stateK, counterexamples,
						true, false));
			} else {
				pq.add(getSuccOfCall(transition, position, state, stateK, counterexamples));
			}
			firstIteration = false;
		}

		if (stateK == mOperand.getEmptyStackState()) {
			// there is no return transition
			return pq;
		}
		for (final STATE stateKk : getCallStatesOfCallState(stateK)) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> returnIterator =
					mOperand.returnSuccessorsGivenHier(state, stateK).iterator();
			while (returnIterator.hasNext()) {
				final OutgoingReturnTransition<LETTER, STATE> transition = returnIterator.next();
				final STATE succ = transition.getSucc();
				if (!exploreThisSuccessor(state, transition.getLetter(), succ)) {
					continue;
				}
				if (firstIteration && !returnIterator.hasNext()) {
					pq.add(new PQState(1, state, transition.getLetter(), transition.getSucc(), stateKk, counterexamples,
							false, true));
				} else {
					pq.add(getSuccOfReturn(transition, position, state, stateKk, counterexamples));
				}
				firstIteration = false;
			}
		}
		return pq;
	}

	private PriorityQueue<PQState> pickStartToExplore(final Collection<STATE> states, final Set<Integer> set) {
		final PriorityQueue<PQState> pq = new PriorityQueue<>(Comparator.comparingInt(PQState::getScore));

		for (final STATE state : states) {
			final ArrayList<Integer> activeCounterexamples = new ArrayList<>();
			int currentScore = 0;
			for (final int cexHash : set) {
				IcfgLocation programPoint = null;

				final STATE stateInCEx = (STATE) mActiveCounterexamples.get(cexHash).getStateAtPosition(0);
				if (stateInCEx instanceof ISLPredicate) {
					programPoint = ((ISLPredicate) stateInCEx).getProgramPoint();
				} else {
					throw new AssertionError("Unexpected Predicate");
				}

				if (programPoint.equals(((ISLPredicate) state).getProgramPoint())) {
					currentScore += 1;
					activeCounterexamples.add(cexHash);
				} else {
					if (mActiveCounterexamples.get(cexHash).getStateAtPosition(0).equals(state)) {
						throw new AssertionError("Program Point mismatch");
					}
				}
			}
			pq.add(new PQState(currentScore, null, null, state, null, activeCounterexamples, false, false));
		}
		return pq;
	}

	/*
	 * Only check if visited after we reached score 0
	 */
	private NestedRun<LETTER, STATE> constructRunFromStateToNextBranch(final int position,
			final DoubleDecker<STATE> pair, final ArrayList<Integer> counterexamples)
			throws AutomataOperationCanceledException {
		mCountRecursionSteps += 1;
		if (System.nanoTime() / 1000000000 > mTimeOut || mTimedout) {
			mTimedout = true;
			mLogger.warn("IsEmpyParallel timeout");
			return null;
		}
		if (mCountRecursionSteps > 700) {
			mTimedout = true;
			mLogger.warn("IsEmpyParallel Recursion Limit");
			return null;
		}
		int positionOfThisSubSearch = position;

		if (!mServices.getProgressAwareTimer().continueProcessing()) {
			final String taskDescription = "searching accepting run (input had " + mOperand.size() + " states)";
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
			throw new AutomataOperationCanceledException(rti);
		}

		positionOfThisSubSearch += 1;
		final STATE state = pair.getUp();
		final STATE stateK = pair.getDown();

		mVisitedPairs.clear(); // reset visited Pairs, then add start of subsearch
		if (counterexamples.isEmpty()) {
			final IsEmptyHeuristic<LETTER, STATE> runsearch;
			if (mGoalStates != null) {
				final Predicate<STATE> funIsForbiddenState = a -> false;
				final Predicate<STATE> goals = a -> mGoalStates.contains(a);
				final Set<STATE> startset = new HashSet<>(mStartStates);
				runsearch = new IsEmptyHeuristic<>(mServices, mOperand, startset, funIsForbiddenState, goals,
						IHeuristic.getHeuristic(AStarHeuristic.ZERO, null, 0), new ArrayList<>(mCurrentPrefix));
			} else {
				runsearch = new IsEmptyHeuristic<>(mServices, mOperand,
						IHeuristic.getHeuristic(AStarHeuristic.ZERO, null, 0), new ArrayList<>(mCurrentPrefix));
			}
			final NestedRun<LETTER, STATE> run = runsearch.getNestedRun();
			if (run == null) {
				return run;
			}
			for (final Integer cexHash : mActiveCounterexamples.keySet()) {
				if (cexHash == run.getWord().asList().hashCode()) {
					throw new AssertionError("Not a fresh counterexample!");
				}
			}
			return run; // is null if isEmpty fails, leads to backtracking
		}

		// equality intended here
		if (stateK != mOperand.getEmptyStackState()) {
			// there is no return transition
			// getAcceptingRunHelperReturn(state, stateK);
		}

		// enqueues successors
		if (!counterexamples.isEmpty()) {

			final PriorityQueue<PQState> pqStart =
					pickSuccToExplore(positionOfThisSubSearch, state, stateK, counterexamples); // statek is not
			if (pqStart.isEmpty()) {
				return null;
			}
			while (!pqStart.isEmpty()) {
				final PQState startpq = pqStart.poll();
				if (startpq == null) {
					throw new AssertionError("No Priority Queue");
				}
				final STATE newState = startpq.getState(); // only needed for summaries
				final STATE newStateK = startpq.getStateK();
				final STATE succ = startpq.getSucc();
				final LETTER symbol = startpq.getLetter();

				NestedRun<LETTER, STATE> runToGoal;
				addToCurrentPrefix(succ, symbol);
				if (startpq.isCall()) {
					markCallVisited(newState, newStateK);
					runToGoal = constructRunFromStateToNextBranch(positionOfThisSubSearch,
							new DoubleDecker<>(newState, succ), startpq.getCounterexamplesUnderConsideration());

					unmarkCall(newState, newStateK);

				} else if (startpq.isReturn()) {
					// stateK is the hierarchical pre of state
					// newStateK is the stateKK
					unmarkCall(stateK, newStateK);
					addSummary(newStateK, succ, newState, symbol);
					runToGoal = constructRunFromStateToNextBranch(positionOfThisSubSearch,
							new DoubleDecker<>(newStateK, succ), startpq.getCounterexamplesUnderConsideration());
					markCallVisited(stateK, newStateK);
				} else {
					runToGoal = constructRunFromStateToNextBranch(positionOfThisSubSearch,
							new DoubleDecker<>(newStateK, succ), startpq.getCounterexamplesUnderConsideration());
				}
				removeFromCurrentPrefix(succ, symbol);
				if (runToGoal != null) {
					return runToGoal;
				}
			}
		}
		mCountRecursionSteps -= 1;
		return null;
	}

	private void addToCurrentPrefix(final STATE state, final LETTER letter) {
		mCurrentPrefix.add(new Pair<>(state, letter));
	}

	private void removeFromCurrentPrefix(final STATE state, final LETTER letter) {
		assert mCurrentPrefix.getLast().getFirst().equals(state) && mCurrentPrefix.getLast().getSecond().equals(letter);
		mCurrentPrefix.removeLast();
	}

	@SuppressWarnings("squid:S1698")
	private NestedRun<LETTER, STATE> getAcceptingRunParallel(final Set<Integer> set)
			throws AutomataOperationCanceledException {
		final PriorityQueue<PQState> pqStart = pickStartToExplore(mStartStates, set);
		// if abstraction is empty, there might not be a start anymore
		while (!pqStart.isEmpty()) {
			final PQState startpq = pqStart.poll();
			final STATE start = startpq.getSucc();
			final NestedRun<LETTER, STATE> runToGoal = constructRunFromStateToNextBranch(0,
					new DoubleDecker<>(mDummyEmptyStackState, start), startpq.getCounterexamplesUnderConsideration());

			if (runToGoal != null) {
				for (final Integer cexHash : set) {
					if (cexHash == runToGoal.getWord().asList().hashCode()) {
						throw new AssertionError("Not a fresh counterexample!");
					}
				}
				return runToGoal;
			}
		}
		return null;
	}

	@Override
	public NestedRun<LETTER, STATE> getNestedRun() {
		if (!getResult()) {
			for (int i = 0; i < mAcceptingRun.getLength() - 1; i++) {
				if (mAcceptingRun.getWord().isPendingReturn(i)) {
					countFailedRunConstruction += 1;
					return null;
				}
			}
		}
		return mAcceptingRun;
	}

	public long getTimeSpend() {
		mTimeSpendSearching = System.nanoTime() / 1000000000 - mStart;
		return mTimeSpendSearching;
	}

	private class PQState {
		final Integer mScore;
		final STATE mState;
		final STATE mSucc;
		final STATE mStateK;
		ArrayList<Integer> mCounterexamples = new ArrayList<>();
		final LETTER mSymbol;
		final boolean mCallTransition;
		final boolean mReturnTransition;

		public PQState(final int score, final STATE state, final LETTER symbol, final STATE succ, final STATE stateK,
				final ArrayList<Integer> counterexamples, final boolean call, final boolean ret) {
			mScore = score;
			mState = state;
			mSucc = succ;
			mStateK = stateK;
			mCounterexamples = counterexamples;
			mSymbol = symbol;
			mCallTransition = call;
			mReturnTransition = ret;
			assert !mCallTransition || !mReturnTransition;
		}

		public Integer getScore() {
			return mScore;
		}

		public STATE getState() {
			return mState;
		}

		public STATE getStateK() {
			return mStateK;
		}

		public STATE getSucc() {
			return mSucc;
		}

		public boolean isCall() {
			return mCallTransition;
		}

		public boolean isReturn() {
			return mReturnTransition;
		}

		public LETTER getLetter() {
			return mSymbol;
		}

		public ArrayList<Integer> getCounterexamplesUnderConsideration() {
			return mCounterexamples;
		}
	}
}
