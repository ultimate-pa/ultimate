/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Class that provides the Buchi acceptance check for nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public final class BuchiAcceptsRecursive<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * Stem of the nested lasso word whose acceptance is checked.
	 */
	private final NestedWord<LETTER> mStem;
	
	/**
	 * Loop of the nested lasso word whose acceptance is checked.
	 */
	private final NestedWord<LETTER> mLoop;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mNwa;
	private final boolean mAccepted;
	
	/**
	 * Check if a Buchi nested word automaton accepts a nested lasso word.
	 * <p>
	 * Returns true iff nlw is accepted by nwa. Note that here a nested lasso
	 * word is always rejected if its loop contains pending returns.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param nlw
	 *            NestedLassoWord whose acceptance is checked
	 * @param nwa
	 *            NestedWordAutomaton which is interpreted as Buchi nested word
	 *            automaton here
	 */
	public BuchiAcceptsRecursive(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final NestedLassoWord<LETTER> nlw) {
		super(services);
		mNwa = nwa;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		
		mStem = nlw.getStem();
		mLoop = nlw.getLoop();
		
		if (!checkInputValidity()) {
			mAccepted = false;
			return;
		}
		
		mAccepted = computeResult(nwa);
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	@Override
	public String operationName() {
		return "BuchiAcceptsRecursive";
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mNwa;
	}
	
	@Override
	public Boolean getResult() {
		return mAccepted;
	}
	
	private boolean checkInputValidity() {
		if (mStem.containsPendingReturns()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("This implementation of Buchi acceptance rejects lasso words where the stem contains "
						+ "pending returns.");
			}
			return false;
		}
		if (mLoop.containsPendingReturns()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("This implementation of Buchi acceptance rejects lasso words where the loop contains "
						+ "pending returns.");
			}
			return false;
			
		}
		
		if (mLoop.length() == 0) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("LassoWords with empty lasso are rejected by every Büchi automaton");
			}
			return false;
		}
		return true;
	}
	
	private boolean computeResult(final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		// First compute all states in which the automaton can be after processing the
		// stem.
		// Honda denotes the part of the lasso where stem and loop are connected.
		// Therefore we call theses stats Honda states.
		final Set<STATE> hondaStates = new HashSet<>();
		final Iterable<STATE> initialStates = nwa.getInitialStates();
		for (final STATE initialState : initialStates) {
			final Set<STATE> reach = getReachableStates(0, initialState, new LinkedList<STATE>());
			hondaStates.addAll(reach);
		}
		
		// Compute for each hondaState if processing mLoop can lead to a run that
		// contains an accepting state and brings the automaton back to the honda state.
		boolean result = false;
		for (final STATE hondaState : hondaStates) {
			result = result || isCompleteableToAcceptingRun(new HashMap<STATE, Boolean>(), 0, hondaState,
					new LinkedList<STATE>());
		}
		
		return result;
	}
	
	/**
	 * Recursive computation of reachable states while processing mStem.
	 * <p>
	 * Assume,
	 * <ul>
	 * <li>we started processing mStem in some state,
	 * <li>we processed mStem until position currentPosition
	 * <li>and ended in state currentState,
	 * <li>while processing, we pushed the current state to callStack whenever we
	 * processed a call position and pop'ed the top element from the callStack whenever
	 * we processed a return position.
	 * </ul>
	 * getReachableStates computes the states that we can reach by processing
	 * mStem further. If the automaton is deterministic this result will always be a
	 * singleton.
	 */
	private Set<STATE> getReachableStates(final int currentPosition, final STATE currentState,
			final List<STATE> callStack) {
		if (currentPosition >= mStem.length()) {
			return Collections.singleton(currentState);
		}
		final LETTER currentSymbol = mStem.getSymbolAt(currentPosition);
		
		final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> outgoingTransitions =
				getOutgoingTransitions(currentPosition, currentState, callStack, currentSymbol, mStem, "stem");
		
		if (!outgoingTransitions.iterator().hasNext()) {
			return Collections.emptySet();
		}
		final List<STATE> succStates = new ArrayList<>();
		for (final IOutgoingTransitionlet<LETTER, STATE> outgoingTransition : outgoingTransitions) {
			succStates.add(outgoingTransition.getSucc());
		}
		final Set<STATE> result = new HashSet<>();
		for (int i = 0; i < succStates.size(); i++) {
			// in case of nondeterminism, i.e. several successor states for
			// currentSymbol, every recursive call of this procedure needs its own
			// copy of the call stack. One of the recursive procedure calls (I decided
			// for the last one) can use the existing copy  of the callStack.
			List<STATE> callStackcopy;
			if (i != succStates.size() - 1) {
				callStackcopy = new LinkedList<>(callStack);
			} else {
				callStackcopy = callStack;
			}
			final Set<STATE> returnValue =
					getReachableStates(currentPosition + 1, succStates.get(i), callStackcopy);
			result.addAll(returnValue);
		}
		return result;
	}
	
	/**
	 * Recursive check for an accepting loop run for the NestedWord mLoop.
	 * Therefore we process mLoop several times (see
	 * examples/Automata/BuchiNWA/BugAccepts). Before reading mLoop, (again)
	 * we store the current state in hondaCandidates. Whenever a
	 * hondaCandidate was visited twice we terminate.
	 * <p>
	 * Assume,
	 * <ul>
	 * <li>before reading mLoop, we have always been in one of the states
	 * stored in the domain of hondaCandidates2visitedFinal,
	 * <li>we processed mLoop until position currentPosition
	 * <li>and ended in state currentState,
	 * <li>since visiting hondaState (for the first time) we visited an
	 * accepting state, iff the image of hondateStates is true.
	 * <li>while processing, we pushed the current state to callStack whenever
	 * we processed a call position and pop'ed the top element from the
	 * callStack whenever we processed a return position.
	 * </ul>
	 * isCompleteableToAcceptingRun gives an answer to the question if
	 * processing mLoop further can (nondeterminism! We have to check all
	 * possibilities) lead to hondaState such that an accepting state was
	 * visited.
	 */
	boolean isCompleteableToAcceptingRun(final Map<STATE, Boolean> hondaCandidates2visitedFinal,
			final int currentPositionIn, final STATE currentState, final List<STATE> callStack) {
		int currentPosition = currentPositionIn;
		assert currentPosition <= mLoop.length();
		if (currentPosition == mLoop.length()) {
			currentPosition = 0;
		}
		if (currentPosition == 0) {
			if (hondaCandidates2visitedFinal.containsKey(currentState)) {
				return hondaCandidates2visitedFinal.get(currentState);
			}
			hondaCandidates2visitedFinal.put(currentState, Boolean.FALSE);
		}
		if (mNwa.isFinal(currentState)) {
			for (final STATE hondaCandidate : hondaCandidates2visitedFinal.keySet()) {
				hondaCandidates2visitedFinal.put(hondaCandidate, Boolean.TRUE);
			}
		}
		
		final LETTER currentSymbol = mLoop.getSymbolAt(currentPosition);
		
		final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> outgoingTransitions =
				getOutgoingTransitions(currentPosition, currentState, callStack, currentSymbol, mLoop, "loop");
		final List<STATE> succStates = new ArrayList<>();
		for (final IOutgoingTransitionlet<LETTER, STATE> outgoingTransition : outgoingTransitions) {
			succStates.add(outgoingTransition.getSucc());
		}
		if (succStates.isEmpty()) {
			return false;
		}
		
		return isCompleteableToAcceptingRunHelper(hondaCandidates2visitedFinal, callStack, currentPosition, succStates);
	}
	
	private boolean isCompleteableToAcceptingRunHelper(final Map<STATE, Boolean> hondaCandidates2visitedFinal,
			final List<STATE> callStack, final int currentPosition, final List<STATE> succStates) {
		boolean result = false;
		for (int i = 0; i < succStates.size(); i++) {
			// in case of nondeterminism, i.e. several successor states for
			// currentSymbol, every recursive call of this procedure needs its own
			// copy of the call stack. One of the recursive procedure calls (I decided
			// for the last one) can use the existing copy  of the callStack.
			List<STATE> callStackCopy;
			Map<STATE, Boolean> hondaCandidatesCopy;
			if (i != succStates.size() - 1) {
				callStackCopy = new LinkedList<>(callStack);
				hondaCandidatesCopy = new HashMap<>(hondaCandidates2visitedFinal);
			} else {
				callStackCopy = callStack;
				hondaCandidatesCopy = hondaCandidates2visitedFinal;
			}
			
			result = result || isCompleteableToAcceptingRun(hondaCandidatesCopy, currentPosition + 1,
					succStates.get(i), callStackCopy);
		}
		return result;
	}
	
	private Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> getOutgoingTransitions(final int currentPosition,
			final STATE currentState, final List<STATE> callStack, final LETTER currentSymbol,
			final NestedWord<LETTER> word, final String name) {
		final Iterable<? extends IOutgoingTransitionlet<LETTER, STATE>> outgoingTransitions;
		if (word.isInternalPosition(currentPosition)) {
			outgoingTransitions = mNwa.internalSuccessors(currentState, currentSymbol);
		} else if (word.isCallPosition(currentPosition)) {
			callStack.add(currentState);
			outgoingTransitions = mNwa.callSuccessors(currentState, currentSymbol);
		} else if (word.isReturnPosition(currentPosition)) {
			assert !callStack.isEmpty() : "restricted to " + name + " without pending return";
			//pop the top element from the callStack
			final STATE linearPred = callStack.remove(callStack.size() - 1);
			outgoingTransitions = mNwa.returnSuccessors(currentState, linearPred, currentSymbol);
		} else {
			throw new IllegalArgumentException();
		}
		return outgoingTransitions;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
