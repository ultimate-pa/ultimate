/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

import java.util.Set;

/**
 * Normalizes state names.
 * 
 * This shrinker renames states in the following way: - All initial states are
 * named "q0_i" for some i. - All other final states are named "qf_i" for some
 * i. - All other states are named "q_i" for some i.
 * 
 * For each of those three types of states the index is a consecutive number,
 * assigned in a depth-first manner starting from some initial state.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class NormalizeStateShrinker<LETTER, STATE>
		extends AShrinker<STATE, LETTER, STATE> {
	@SuppressWarnings("squid:UselessParenthesesCheck")
	@Override
	public INestedWordAutomaton<LETTER, STATE>
			createAutomaton(final List<STATE> list) {
		// create fresh automaton
		final INestedWordAutomaton<LETTER, STATE> automaton =
				mFactory.create(mAutomaton);
		
		// rename states
		final HashMap<STATE, STATE> old2new = renameStates(automaton, list);
		
		// add transitions
		addTransitions(automaton, old2new);
		
		return automaton;
	}
	
	/**
	 * depth-first renaming of states
	 * 
	 * @param automaton automaton
	 * @param list list of states
	 * @return map old state -> new state
	 */
	@SuppressWarnings({ "unchecked", "squid:UselessParenthesesCheck" })
	private HashMap<STATE, STATE> renameStates(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final List<STATE> list) {
		final HashSet<STATE> noninitialStates = new HashSet<STATE>();
		final ArrayDeque<STATE> stack = new ArrayDeque<STATE>();
		final HashSet<STATE> remaining =
				filterStates(list, noninitialStates, stack);
		final Set<STATE> oldStates = mAutomaton.getStates();
		
		final HashMap<STATE, STATE> old2new = new HashMap<STATE, STATE>();
		final HashSet<STATE> onStackOrVisited = new HashSet<STATE>(stack);
		int initials = 0;
		int finals = 0;
		int normals = 0;
		boolean firstRun = true;
		while (true) {
			// check whether stack is empty
			if (stack.isEmpty()) {
				if (firstRun) {
					// the first time the stack is empty is ok
					firstRun = false;
					addMissingStates(noninitialStates, stack,
							remaining, onStackOrVisited);
					continue;
				} else {
					// stop when the stack is empty a second time
					break;
				}
			}
			
			// pick the next state
			final STATE oldState = stack.pop();
			
			final boolean isInitial = mAutomaton.isInitial(oldState);
			final boolean isFinal = mAutomaton.isFinal(oldState);
			
			// create new state if not already present
			final STATE newState;
			if (remaining.remove(oldState)) {
				// do not reassign this state name (was not in the list)
				newState = oldState;
			} else {
				/*
				 * assign new name
				 * Make sure that the new state name does not exist.
				 */
				assert (oldState instanceof String) : "The state was a " +
						"string during list creation.";
				STATE newStateCandidate = null;
				if (isInitial) {
					do {
						++initials;
						newStateCandidate = (STATE) ("qI_" + initials);
					} while (isUsedName(newStateCandidate, oldState, oldStates));
				} else if (isFinal) {
					do {
						++finals;
						newStateCandidate = (STATE) ("qF_" + finals);
					} while (isUsedName(newStateCandidate, oldState, oldStates));
				} else {
					do {
						++normals;
						newStateCandidate = (STATE) ("q_" + normals);
					} while (isUsedName(newStateCandidate, oldState, oldStates));
				}
				newState = newStateCandidate;
			}
			final STATE oldMapping = old2new.put(oldState, newState);
			assert (oldMapping == null);
			mFactory.addState(automaton, newState, isInitial, isFinal);
			
			// push successors which have not been visited
			considerSuccessors(stack, onStackOrVisited, oldState);
		}
		assert (automaton.size() == mAutomaton.size()) : "The number of " +
				"states must be retained.";
		return old2new;
	}
	
	private boolean isUsedName(final STATE newStateCandidate,
			final STATE oldState, final Set<STATE> oldStates) {
		if (oldStates.contains(newStateCandidate)) {
			return (! oldState.equals(newStateCandidate));
		}
		return false;
	}

	/**
	 * preprocessing: filters states into initial and non-initial states
	 * and returns the set of states not in the list
	 * 
	 * @param list list of states (input)
	 * @param noninitialStates set of non-initial states
	 * @param initialStates stack of initial states
	 * @return remaining original states not visited
	 */
	private HashSet<STATE> filterStates(final List<STATE> list,
			final HashSet<STATE> noninitialStates,
			final ArrayDeque<STATE> initialStates) {
		final HashSet<STATE> remaining =
				new HashSet<STATE>(mAutomaton.getStates());
		
		for (final STATE state : list) {
			final boolean wasPresent = remaining.remove(state);
			assert wasPresent;
			if (mAutomaton.isInitial(state)) {
				initialStates.add(state);
			} else {
				noninitialStates.add(state);
			}
		}
		
		return remaining;
	}
	
	/**
	 * adds states not reached by a forward search (might be necessary for the
	 * bug to occur)
	 * 
	 * @param noninitialStates non-initial states
	 * @param stack stack of states (empty when this method is called)
	 * @param remaining states not visited yet
	 * @param onStackOrVisited states on stack or visited
	 */
	private void addMissingStates(final HashSet<STATE> noninitialStates,
			final ArrayDeque<STATE> stack, final HashSet<STATE> remaining,
			final HashSet<STATE> onStackOrVisited) {
		for (final STATE state : noninitialStates) {
			if (onStackOrVisited.add(state)) {
				stack.push(state);
			}
		}
		for (final STATE state : remaining) {
			final boolean wasNotPresent = onStackOrVisited.add(state);
			assert wasNotPresent;
			stack.add(state);
		}
	}
	
	/**
	 * adds all successor states which have not been visited
	 * 
	 * @param stack stack of states
	 * @param onStackOrVisited states on stack or visited
	 * @param oldState state in the old automaton
	 */
	private void considerSuccessors(final ArrayDeque<STATE> stack,
			final HashSet<STATE> onStackOrVisited, final STATE oldState) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mAutomaton
				.internalSuccessors(oldState)) {
			final STATE succ = trans.getSucc();
			checkAndAddSuccessor(stack, onStackOrVisited, succ);
		}
		for (final OutgoingCallTransition<LETTER, STATE> trans : mAutomaton
				.callSuccessors(oldState)) {
			final STATE succ = trans.getSucc();
			checkAndAddSuccessor(stack, onStackOrVisited, succ);
		}
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mAutomaton
				.returnSuccessors(oldState)) {
			final STATE succ = trans.getSucc();
			checkAndAddSuccessor(stack, onStackOrVisited, succ);
		}
	}
	
	/**
	 * checks whether the successor is in a set; if not, adds the state to the
	 * set and a stack
	 * 
	 * @param stack stack to push to
	 * @param onStackOrVisited set of states (if state not present, add it)
	 * @param succ
	 */
	private void checkAndAddSuccessor(final ArrayDeque<STATE> stack,
			final HashSet<STATE> onStackOrVisited, final STATE succ) {
		if (onStackOrVisited.add(succ)) {
			stack.push(succ);
		}
	}
	
	/**
	 * adds transitions for new states
	 * 
	 * @param automaton automaton
	 * @param old2new map old state -> new state
	 */
	private void addTransitions(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final HashMap<STATE, STATE> old2new) {
		// add transitions
		for (final Entry<STATE, STATE> entry : old2new.entrySet()) {
			final STATE oldState = entry.getKey();
			final STATE newState = entry.getValue();
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mAutomaton
					.internalSuccessors(oldState)) {
				mFactory.addInternalTransition(automaton, newState,
						trans.getLetter(), old2new.get(trans.getSucc()));
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : mAutomaton
					.callSuccessors(oldState)) {
				mFactory.addCallTransition(automaton, newState,
						trans.getLetter(), old2new.get(trans.getSucc()));
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mAutomaton
					.returnSuccessors(oldState)) {
				mFactory.addReturnTransition(automaton, newState,
						old2new.get(trans.getHierPred()), trans.getLetter(),
						old2new.get(trans.getSucc()));
			}
		}
	}
	
	@Override
	public List<STATE> extractList() {
		final Set<STATE> states = mAutomaton.getStates();
		final Iterator<STATE> iterator = states.iterator();
		if ((iterator.hasNext()) && (iterator.next() instanceof String)) {
			// states of type string can be renamed
			return new ArrayList<STATE>(states);
		}
		// no states or of non-string type cannot be renamed
		return new ArrayList<STATE>();
	}
}
