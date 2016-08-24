/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.Utils;

/**
 * Check emptiness and obtain an accepting run of a nested word automaton.
 * The algorithm computes a reachability graph. The nodes of the graph describe
 * a configuration of the automaton. They are represented by state pairs
 * (state,stateK) where state is the "current state" in the reachability
 * analysis of the automaton, stateK is the last state before the last call
 * transition. If we consider the automaton as a machine with a stack, stateK
 * is the topmost element of the stack.
 * The edges of the reachability graph are labeled with runs of length two or
 * summary.
 * The reachability graph is obtained by traversing the automaton in a BFS
 * manner.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class IsEmpty<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * Set of states in which the run we are searching has to begin.
	 */
	private final Collection<STATE> mStartStates;
	
	/**
	 * Set of states in which the run we are searching has to end.
	 */
	private final Collection<STATE> mGoalStates;
	
	/**
	 * If set, the goal states are exactly the accepting states of automaton
	 * mnwa, the set mGoalStates is null, and we use mnwa to check if a
	 * state is a goal state.
	 */
	private final boolean mGoalStateIsAcceptingState;
	
	/**
	 * Set of states in which the run we are searching must not visit.
	 */
	private final Collection<STATE> mForbiddenStates;
	
	private final NestedRun<LETTER, STATE> mAcceptingRun;
	
	/**
	 * Pairs of states visited, but possibly not processed, so far.
	 */
	private final Map<STATE, Set<STATE>> mVisitedPairs =
			new HashMap<STATE, Set<STATE>>();
			
	/**
	 * Queue of states that have to be processed and have been visited while
	 * processing a internal transition, a return transition or a computed
	 * summary.
	 */
	private final LinkedList<DoubleDecker<STATE>> mQueue =
			new LinkedList<DoubleDecker<STATE>>();
			
	/**
	 * Queue of states that have to be processed and have been visited while
	 * processing a call transition.
	 */
	private final LinkedList<DoubleDecker<STATE>> mQueueCall =
			new LinkedList<DoubleDecker<STATE>>();
			
	/**
	 * Assigns to a pair of states (state,stateK) the run of length 2 that is
	 * labeled to the incoming edge of (state,stateK) in the reachability graph.
	 * The symbol of the run has to be an internal symbol. The predecessor of
	 * (state,stateK) in the reachability graph is (pred,predK), where pred is
	 * the first state of the run and predK is stateK.
	 */
	private final Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>> mInternalSubRun =
			new HashMap<STATE, Map<STATE, NestedRun<LETTER, STATE>>>();
			
	/**
	 * Assigns to a triple of states (state,stateK,predK) the run of length 2
	 * that is labeled to the incoming edge of the state pair (state,stateK)
	 * in the reachability graph. The symbol of the run has to be a call symbol.
	 * The predecessor of (state,stateK) in the reachability graph is
	 * (pred,predK), where pred is stateK.
	 */
	private final Map<STATE, Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>>> mCallSubRun =
			new HashMap<STATE, Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>>>();
			
	/**
	 * Assigns to a pair of states (state,stateK) a state predK. predK is the
	 * second component of the state pair (pred,predK) for which (state,stateK)
	 * was added to the reachability graph (for the first time).
	 */
	private final Map<STATE, Map<STATE, STATE>> mCallFirst =
			new HashMap<STATE, Map<STATE, STATE>>();
			
	/**
	 * Assigns to a pair of states (state,stateK) the run of length 2 that is
	 * labeled to the incoming edge of (state,stateK) in the reachability graph.
	 * The symbol of the run has to be a return symbol. The predecessor of
	 * (state,stateK) in the reachability graph is (pred,predK), where pred is
	 * the first state of the run. predK can be obtained from mreturnPredStateK
	 */
	private final Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>> mReturnSubRun =
			new HashMap<STATE, Map<STATE, NestedRun<LETTER, STATE>>>();
			
	/**
	 * Assigns to a pair of states (state,stateK) a state predK. predK is the
	 * second component of the predecessor (pred,predK) of (state,stateK) in the
	 * reachability graph.
	 */
	private final Map<STATE, Map<STATE, STATE>> mReturnPredStateK =
			new HashMap<STATE, Map<STATE, STATE>>();
			
	/**
	 * If a triple (state,succ,returnPred) is contained in this map, a summary
	 * from state to succ has been discovered and returnPred is the predecessor
	 * of the return transition of this summary.
	 */
	private final Map<STATE, Map<STATE, STATE>> mSummaryReturnPred =
			new HashMap<STATE, Map<STATE, STATE>>();
			
	/**
	 * If a triple (state,succ,symbol) is contained in this map, a summary
	 * from state to succ has been discovered and symbol is the label of the
	 * return transition of this summary.
	 */
	private final Map<STATE, Map<STATE, LETTER>> mSummaryReturnSymbol =
			new HashMap<STATE, Map<STATE, LETTER>>();
			
	/**
	 * Second Element of the initial state pair. This state indicates that
	 * nothing is on the stack of the automaton, in other words while processing
	 * we have taken the same number of calls and returns.
	 */
	private final STATE mDummyEmptyStackState;
	
	/**
	 * Stack for the constructing a run if non-emptiness was detected. Contains
	 * an element for every return that was processed and to corresponding call
	 * was processed yet.
	 * Corresponds to the stack-of-returned-elements-that-have-not-been-called
	 * of the automaton but all elements are shifted by one.
	 */
	private final ArrayDeque<STATE> mReconstructionStack = new ArrayDeque<STATE>();
	
	private NestedRun<LETTER, STATE> mReconstructionOneStepRun;
	
	private STATE mReconstructionPredK;
	
	/**
	 * Default constructor. Here we search a run from the initial states
	 * of the automaton to the final states of the automaton.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 */
	public IsEmpty(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		super(services, operand);
		mDummyEmptyStackState = mOperand.getEmptyStackState();
		mStartStates = Utils.constructHashSet(mOperand.getInitialStates());
		mGoalStateIsAcceptingState = true;
		mGoalStates = null;
		mForbiddenStates = Collections.emptySet();
		mLogger.info(startMessage());
		mAcceptingRun = getAcceptingRun();
		mLogger.info(exitMessage());
	}
	
	/**
	 * Constructor that is not restricted to emptiness checks.
	 * The set of startStates defines where the run that we search has to start.
	 * The set of forbiddenStates defines states that the run must not visit.
	 * The set of goalStates defines where the run that we search has to end.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @param startStates
	 *            start states
	 * @param forbiddenStates
	 *            forbidden states
	 * @param goalStates
	 *            goal states
	 */
	public IsEmpty(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Set<STATE> startStates, final Set<STATE> forbiddenStates,
			final Set<STATE> goalStates) {
		super(services, operand);
		assert operand.getStates().containsAll(startStates) : "unknown states";
		assert operand.getStates().containsAll(goalStates) : "unknown states";
		mDummyEmptyStackState = mOperand.getEmptyStackState();
		mStartStates = startStates;
		mGoalStateIsAcceptingState = false;
		mGoalStates = goalStates;
		mForbiddenStates = forbiddenStates;
		mLogger.info(startMessage());
		mAcceptingRun = getAcceptingRun();
		mLogger.info(exitMessage());
	}
	
	/**
	 * If we use the accepting states of mnwa as goal states (in this case
	 * mGoalStateIsAcceptingState is set and mGoalStates is null) then we
	 * return true iff state is an accepting state.
	 * Otherwise we return true iff mGoalStates.contains(state).
	 */
	private boolean isGoalState(final STATE state) {
		if (mGoalStateIsAcceptingState) {
			assert mGoalStates == null : "if we search accepting states, mGoalStates is null";
			return mOperand.isFinal(state);
		} else {
			return mGoalStates.contains(state);
		}
	}
	
	/**
	 * Enqueue a state pair that has been discovered by taking an internal
	 * transition, a return transition or a summary. Mark the state pair as
	 * visited afterwards.
	 */
	private void enqueueAndMarkVisited(final STATE state, final STATE stateK) {
		final DoubleDecker<STATE> pair = new DoubleDecker<STATE>(stateK, state);
		mQueue.addLast(pair);
		markVisited(state, stateK);
	}
	
	/**
	 * Enqueue a state pair that has been discovered by taking a call
	 * transition. Mark the state pair as visited afterwards.
	 */
	private void enqueueAndMarkVisitedCall(final STATE state, final STATE callPred) {
		final DoubleDecker<STATE> pair = new DoubleDecker<STATE>(callPred, state);
		mQueueCall.addLast(pair);
		markVisited(state, callPred);
	}
	
//  The following implementation of dequeue is faster but leads to unsound
//	results. See BugBfsEmptinessLowPriorityCallQueue.fat for details.
//  Alternative workaround (where we may still use the low priority call queue):
//  When final state is reached, process the whole call queue before
//  computation of accepting run.
//	/**
//	 * Dequeue a state pair. If available take a state pair that has been
//	 * discovered by taking an internal transition, a return transition or a
//	 * summary. If not take a state pair that has been discovered by taking a
//	 * call transition.
//	 */
//	private IState<LETTER,STATE>[] dequeue() {
//		if (!mqueue.isEmpty()) {
//			return mqueue.removeFirst();
//		}
//		else {
//			return mqueueCall.removeFirst();
//		}
//	}
	/**
	 * Dequeue a state pair. If available take a state pair that has been
	 * discovered by taking a
	 * call transition. If not take a state pair that has been discovered by
	 * taking an internal transition, a return transition or a
	 * summary.
	 */
	private DoubleDecker<STATE> dequeue() {
		if (!mQueueCall.isEmpty()) {
			return mQueueCall.removeFirst();
		} else {
			return mQueue.removeFirst();
		}
	}
	
	/**
	 * @return true iff the queue (is internally represented by two queues) is empty.
	 */
	private boolean isQueueEmpty() {
		return mQueue.isEmpty() && mQueueCall.isEmpty();
	}
	
	/**
	 * Mark a state pair a visited.
	 */
	private void markVisited(final STATE state, final STATE stateK) {
		Set<STATE> callPreds = mVisitedPairs.get(state);
		if (callPreds == null) {
			callPreds = new HashSet<STATE>();
			mVisitedPairs.put(state, callPreds);
		}
		callPreds.add(stateK);
	}
	
	/**
	 * @return true iff the state pair (state,stateK) was already visited.
	 */
	private boolean wasVisited(final STATE state, final STATE stateK) {
		final Set<STATE> callPreds = mVisitedPairs.get(state);
		if (callPreds == null) {
			return false;
		} else {
			return callPreds.contains(stateK);
		}
	}
	
	/**
	 * Get an accepting run of the automaton passed to the constructor. Return
	 * null if the automaton does not accept any nested word.
	 */
	private NestedRun<LETTER, STATE> getAcceptingRun() {
		for (final STATE state : mStartStates) {
			enqueueAndMarkVisited(state, mDummyEmptyStackState);
		}
		
		while (!isQueueEmpty()) {
			final DoubleDecker<STATE> pair = dequeue();
			final STATE state = pair.getUp();
			final STATE stateK = pair.getDown();
			
			if (isGoalState(state)) {
				return constructRun(state, stateK);
			}
			
			processSummaries(state, stateK);
			
			for (final OutgoingInternalTransition<LETTER, STATE> internalTransition : mOperand
					.internalSuccessors(state)) {
				final LETTER symbol = internalTransition.getLetter();
				final STATE succ = internalTransition.getSucc();
				if (!mForbiddenStates.contains(succ)) {
					if (!wasVisited(succ, stateK)) {
						addRunInformationInternal(
								succ, stateK, symbol, state, stateK);
						enqueueAndMarkVisited(succ, stateK);
					}
				}
			}
			
			for (final OutgoingCallTransition<LETTER, STATE> callTransition : mOperand.callSuccessors(state)) {
				final LETTER symbol = callTransition.getLetter();
				final STATE succ = callTransition.getSucc();
				if (!mForbiddenStates.contains(succ)) {
					//add these information even in already visited
					addRunInformationCall(succ, state, symbol, state, stateK);
					if (!wasVisited(succ, state)) {
						enqueueAndMarkVisitedCall(succ, state);
					}
				}
			}
			
			if (stateK == mOperand.getEmptyStackState()) {
				//there is no return transition
				continue;
			}
			
			for (final OutgoingReturnTransition<LETTER, STATE> returnTransition : mOperand
					.returnSuccessorsGivenHier(state, stateK)) {
				final LETTER symbol = returnTransition.getLetter();
				final STATE succ = returnTransition.getSucc();
				if (!mForbiddenStates.contains(succ)) {
					for (final STATE stateKK : getCallStatesOfCallState(stateK)) {
						addSummary(stateK, succ, state, symbol);
						if (!wasVisited(succ, stateKK)) {
							enqueueAndMarkVisited(succ, stateKK);
							addRunInformationReturn(succ, stateKK, symbol, state, stateK);
						}
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Compute successor state pairs (succ,succK) of the state pair
	 * (state,stateK) under an already discovered summary in the reachability
	 * graph.
	 * succK is stateK. For adding run information for (succ,succK) information
	 * about the summary is fetched.
	 */
	private void processSummaries(final STATE state, final STATE stateK) {
		if (mSummaryReturnPred.containsKey(state)) {
			assert (mSummaryReturnSymbol.containsKey(state));
			final Map<STATE, STATE> succ2ReturnPred =
					mSummaryReturnPred.get(state);
			final Map<STATE, LETTER> succ2ReturnSymbol =
					mSummaryReturnSymbol.get(state);
			for (final Entry<STATE, STATE> entry : succ2ReturnPred.entrySet()) {
				final STATE succ = entry.getKey();
				assert (succ2ReturnSymbol.containsKey(succ));
				final STATE returnPred = entry.getValue();
				final LETTER symbol = succ2ReturnSymbol.get(succ);
				if (!wasVisited(succ, stateK)) {
					enqueueAndMarkVisited(succ, stateK);
					addRunInformationReturn(
							succ, stateK, symbol, returnPred, state);
				}
			}
			
		}
		
	}
	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under an internal transition and a
	 * run of length two from state to succ.
	 */
	private void addRunInformationInternal(final STATE succ,
			final STATE succK,
			final LETTER symbol,
			final STATE state,
			final STATE stateK) {
		Map<STATE, NestedRun<LETTER, STATE>> succK2run =
				mInternalSubRun.get(succ);
		if (succK2run == null) {
			succK2run = new HashMap<STATE, NestedRun<LETTER, STATE>>();
			mInternalSubRun.put(succ, succK2run);
		}
		assert (succK2run.get(succK) == null);
		final NestedRun<LETTER, STATE> run = new NestedRun<LETTER, STATE>(
				state, symbol, NestedWord.INTERNAL_POSITION, succ);
		succK2run.put(succK, run);
	}
	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under a call transition and a
	 * run of length two from state to succ.
	 * If (succ,succK) was visited for the first time, store also stateK in
	 * mcallFirst.
	 */
	private void addRunInformationCall(final STATE succ,
			final STATE succK,
			final LETTER symbol,
			final STATE state,
			final STATE stateK) {
//		mLogger.debug("Call SubrunInformation: From ("+succ+","+succK+
//			") can go to ("+state+","+stateK+")");
		assert (state == succK);
		Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>> succK2stateK2Run =
				mCallSubRun.get(succ);
		Map<STATE, STATE> succK2FirstStateK =
				mCallFirst.get(succ);
		if (succK2stateK2Run == null) {
			succK2stateK2Run =
					new HashMap<STATE, Map<STATE, NestedRun<LETTER, STATE>>>();
			mCallSubRun.put(succ, succK2stateK2Run);
			succK2FirstStateK = new HashMap<STATE, STATE>();
			mCallFirst.put(succ, succK2FirstStateK);
		}
		if (!succK2FirstStateK.containsKey(succK)) {
			succK2FirstStateK.put(succK, stateK);
		}
		Map<STATE, NestedRun<LETTER, STATE>> stateK2Run =
				succK2stateK2Run.get(succK);
		if (stateK2Run == null) {
			stateK2Run = new HashMap<STATE, NestedRun<LETTER, STATE>>();
			succK2stateK2Run.put(succK, stateK2Run);
		}
//		The following assertion is wrong, there can be a two different call
//		transitions from stateK to state. (But in this case we always want to
//		take the one that was first discovered.)
//		assert (!stateK2Run.containsKey(stateK));
		final NestedRun<LETTER, STATE> run =
				new NestedRun<LETTER, STATE>(state, symbol, NestedWord.PLUS_INFINITY, succ);
		stateK2Run.put(stateK, run);
	}
	
	/**
	 * Store for a state pair (succ,succK) in the reachability graph information
	 * about the predecessor (state,stateK) under a return transition and a
	 * run of length two from state to succ.
	 * Store also succK to mreturnPredStateK.
	 */
	private void addRunInformationReturn(final STATE succ,
			final STATE succK,
			final LETTER symbol,
			final STATE state,
			final STATE stateK) {
		Map<STATE, NestedRun<LETTER, STATE>> succK2SubRun =
				mReturnSubRun.get(succ);
		Map<STATE, STATE> succK2PredStateK =
				mReturnPredStateK.get(succ);
		if (succK2SubRun == null) {
			assert (succK2PredStateK == null);
			succK2SubRun = new HashMap<STATE, NestedRun<LETTER, STATE>>();
			mReturnSubRun.put(succ, succK2SubRun);
			succK2PredStateK = new HashMap<STATE, STATE>();
			mReturnPredStateK.put(succ, succK2PredStateK);
		}
		assert (!succK2SubRun.containsKey(succK));
		assert (!succK2PredStateK.containsKey(succK));
		final NestedRun<LETTER, STATE> run =
				new NestedRun<LETTER, STATE>(state, symbol, NestedWord.MINUS_INFINITY, succ);
		succK2SubRun.put(succK, run);
		succK2PredStateK.put(succK, stateK);
	}
	
	/**
	 * Get all states which occur as the second component of a state pair
	 * (callState,*) in the reachability graph, where the first component is
	 * callState.
	 */
	private Set<STATE> getCallStatesOfCallState(final STATE callState) {
		final Set<STATE> callStatesOfCallStates = mVisitedPairs.get(callState);
		if (callStatesOfCallStates == null) {
			return new HashSet<STATE>(0);
		} else {
			return callStatesOfCallStates;
		}
	}
	
//	private void addCallStatesOfCallState(IState<LETTER,STATE> callState,
//			                              IState<LETTER,STATE> callStateOfCallState) {
//		Set<IState<LETTER,STATE>> callStatesOfCallStates =
//							mCallStatesOfCallState.get(callState);
//		if (callStatesOfCallStates == null) {
//			callStatesOfCallStates = new HashSet<IState<LETTER,STATE>>();
//			mCallStatesOfCallState.put(callState,callStatesOfCallStates);
//		}
//		callStatesOfCallStates.add(callStateOfCallState);
//	}
	
	/**
	 * Store information about a discovered summary.
	 */
	private void addSummary(final STATE stateBeforeCall,
			final STATE stateAfterReturn,
			final STATE stateBeforeReturn,
			final LETTER returnSymbol) {
		Map<STATE, STATE> succ2ReturnPred =
				mSummaryReturnPred.get(stateBeforeCall);
		Map<STATE, LETTER> succ2ReturnSymbol =
				mSummaryReturnSymbol.get(stateBeforeCall);
		if (succ2ReturnPred == null) {
			assert (succ2ReturnSymbol == null);
			succ2ReturnPred = new HashMap<STATE, STATE>();
			mSummaryReturnPred.put(stateBeforeCall, succ2ReturnPred);
			succ2ReturnSymbol = new HashMap<STATE, LETTER>();
			mSummaryReturnSymbol.put(stateBeforeCall, succ2ReturnSymbol);
			
		}
		//update only if there is not already an entry
		if (!succ2ReturnPred.containsKey(stateAfterReturn)) {
			succ2ReturnPred.put(stateAfterReturn, stateBeforeReturn);
			assert (!succ2ReturnSymbol.containsKey(stateAfterReturn));
			succ2ReturnSymbol.put(stateAfterReturn, returnSymbol);
		}
	}
	
	/**
	 * Construct a run for a discovered final state in the reachability
	 * analysis. The run is constructed backwards using the information of
	 * predecessors in the reachability graph and the corresponding runs of
	 * length two.
	 */
	private NestedRun<LETTER, STATE> constructRun(STATE state, STATE stateK) {
//		mLogger.debug("Reconstruction from " + state + " " + stateK);
		NestedRun<LETTER, STATE> run = new NestedRun<LETTER, STATE>(state);
		while (!mStartStates.contains(state) || !mReconstructionStack.isEmpty()) {
			if (computeInternalSubRun(state, stateK)) {
			} else if (computeCallSubRun(state, stateK)) {
			} else if (computeReturnSubRun(state, stateK)) {
			} else {
				mLogger.warn("No Run ending in pair " + state + "  " + stateK
						+ " with reconstructionStack" + mReconstructionStack);
				throw new AssertionError();
			}
			run = mReconstructionOneStepRun.concatenate(run);
			state = run.getStateAtPosition(0);
			stateK = mReconstructionPredK;
		}
		return run;
	}
	
	/**
	 * Return true iff the run that lead to the accepting state contains an
	 * internal transition which is succeeded by state and where stateK is the
	 * topmost stack element.
	 */
	private boolean computeInternalSubRun(final STATE state, final STATE stateK) {
		final Map<STATE, NestedRun<LETTER, STATE>> k2InternalMap =
				mInternalSubRun.get(state);
		if (k2InternalMap != null) {
			final NestedRun<LETTER, STATE> run = k2InternalMap.get(stateK);
			if (run != null) {
				mReconstructionOneStepRun = run;
				mReconstructionPredK = stateK;
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Return true iff the run that lead to the accepting state contains a
	 * call transition which is succeeded by state and where stateK is the
	 * topmost stack element.
	 */
	private boolean computeCallSubRun(final STATE state, final STATE stateK) {
		final Map<STATE, Map<STATE, NestedRun<LETTER, STATE>>> k2CallMap =
				mCallSubRun.get(state);
		if (k2CallMap != null) {
			final Map<STATE, NestedRun<LETTER, STATE>> callMap = k2CallMap.get(stateK);
			if (callMap != null) {
				if (mReconstructionStack.isEmpty()) {
					final STATE predK = mCallFirst.get(state).get(stateK);
					mReconstructionPredK = predK;
					mReconstructionOneStepRun = callMap.get(predK);
					return true;
				} else {
					final STATE predKcandidate = mReconstructionStack.peek();
					if (callMap.containsKey(predKcandidate)) {
						mReconstructionOneStepRun = callMap.get(predKcandidate);
						mReconstructionPredK = predKcandidate;
						mReconstructionStack.pop();
						return true;
					}
//					throw new AssertionError();
				}
			}
		}
		return false;
	}
	
	/**
	 * Return true iff the run that lead to the accepting state contains a
	 * return transition which is succeeded by state and where stateK is the
	 * topmost stack element.
	 */
	private boolean computeReturnSubRun(final STATE state, final STATE stateK) {
		final Map<STATE, NestedRun<LETTER, STATE>> succK2SubRun =
				mReturnSubRun.get(state);
		if (succK2SubRun != null) {
			final Map<STATE, STATE> succK2PredStateK =
					mReturnPredStateK.get(state);
			assert (succK2PredStateK != null);
			final NestedRun<LETTER, STATE> run = succK2SubRun.get(stateK);
			final STATE predK = succK2PredStateK.get(stateK);
			if (run != null) {
				mReconstructionStack.push(stateK);
				mReconstructionOneStepRun = run;
				mReconstructionPredK = predK;
				return true;
			}
		}
		return false;
	}
	
	@Override
	public Boolean getResult() {
		return mAcceptingRun == null;
	}
	
	public NestedRun<LETTER, STATE> getNestedRun() throws AutomataOperationCanceledException {
		return mAcceptingRun;
	}
	
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean correct = true;
		if (mAcceptingRun == null) {
			mLogger.warn("Emptiness not double checked ");
		} else {
			mLogger.warn("Correctness of emptinessCheck not tested.");
			correct = (new Accepts<LETTER, STATE>(mServices, mOperand, mAcceptingRun.getWord())).getResult();
			mLogger.info("Finished testing correctness of emptinessCheck");
		}
		return correct;
	}
	
	@Override
	public String operationName() {
		return "isEmpty";
	}
	
	@Override
	public String exitMessage() {
		if (mAcceptingRun == null) {
			return "Finished " + operationName()
					+ ". No accepting run.";
		} else {
			return "Finished " + operationName()
					+ ". Found accepting run of length " + mAcceptingRun.getLength();
		}
	}
}
