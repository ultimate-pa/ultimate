/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Check if an automaton is 
 * <a href="https://en.wikipedia.org/wiki/Semi-deterministic_B%C3%BCchi_automaton">Semi-deterministic</a>.
 * @author Matthias Heizmann
 */
public class IsSemiDeterministic<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	
	private final Set<STATE> mNondeterministicSuccessorOfAccepting = new HashSet<>();

	private final boolean mResult;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mNwa;
	
	
	@Override
	public String operationName() {
		return "isSemiDeterministic";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			mNwa.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand is " 
					+ (mResult ? "" : "not") + "semideterministic."
					+ " There are " + mNondeterministicSuccessorOfAccepting + 
					"nondeterministic non-strict successor of accepting states."; 
	}
	
	
	public IsSemiDeterministic(AutomataLibraryServices services,
			INestedWordAutomatonSimple<LETTER,STATE> input) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		if (input instanceof NestedWordAutomatonReachableStates) {
			mNwa = (NestedWordAutomatonReachableStates<LETTER, STATE>) input;
		} else {
			mNwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, input);
		}
		mLogger.info(startMessage());
		iterate();
		mResult = mNondeterministicSuccessorOfAccepting.isEmpty();
		mLogger.info(exitMessage());
	}
	
	public void iterate() {
		final Set<DoubleDecker<STATE>> visited = new HashSet<>();
		final ArrayDeque<DoubleDecker<STATE>> worklist = new ArrayDeque<>();
		
		// step one: start with finals,
		//           add all non-call successors
		{
			final Set<DoubleDecker<STATE>> finalDoubleDeckers = getFinalDoubleDeckers();
			visited.addAll(finalDoubleDeckers);
			worklist.addAll(finalDoubleDeckers);
		}
		while (!worklist.isEmpty()) {
			final DoubleDecker<STATE> dd = worklist.remove();
			if (isNondeterministic(dd, mNwa)) {
				mNondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			final Set<DoubleDecker<STATE>> succs = getNonCallSuccessors(dd, mNwa);
			for (final DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}

		// step two: start with yet visited DoubleDeckers, 
		//           add all non-return successors
		{
			worklist.addAll(visited);
		}
		while (!worklist.isEmpty()) {
			final DoubleDecker<STATE> dd = worklist.remove();
			if (isNondeterministic(dd, mNwa)) {
				mNondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			final Set<DoubleDecker<STATE>> succs = getNonReturnSuccessors(dd, mNwa);
			for (final DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}
		
	}
	
	private Set<DoubleDecker<STATE>> getFinalDoubleDeckers() {
		final Set<DoubleDecker<STATE>> result = new HashSet<>();
		for (final STATE fin : mNwa.getFinalStates()) {
			for (final STATE down : mNwa.getDownStates(fin)) {
				result.add(new DoubleDecker<STATE>(down, fin));
			}
		}
		return result;
	}


	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonCallSuccessors(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		final Set<DoubleDecker<STATE>> succs = new HashSet<DoubleDecker<STATE>>();
		for (final OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (final SummaryReturnTransition<LETTER, STATE> out : nwa.returnSummarySuccessor(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (final OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessorsGivenHier(dd.getUp(), dd.getDown())) {
			for (final STATE downOfHier : nwa.getDownStates(dd.getDown())) {
				succs.add(new DoubleDecker<STATE>(downOfHier, out.getSucc()));
			}
		}
		return succs;
	}
	
	
	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonReturnSuccessors(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		final Set<DoubleDecker<STATE>> succs = new HashSet<DoubleDecker<STATE>>();
		for (final OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (final SummaryReturnTransition<LETTER, STATE> out : nwa.returnSummarySuccessor(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (final OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getUp(), out.getSucc()));
		}
		return succs;
	}

	

	public static <LETTER, STATE> boolean isNondeterministic(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> traversedNwa) {
		final boolean isNondeterministicInternal = isNondeterministicInternal(dd.getUp(), traversedNwa);
		final boolean isNondeterministicCall = isNondeterministicCall(dd.getUp(), traversedNwa);
		final boolean isNondeterministicReturn = isNondeterministicReturnGivenHier(dd.getUp(), dd.getDown(), traversedNwa);
		return isNondeterministicInternal || isNondeterministicCall || isNondeterministicReturn;
	}
	
	public static <LETTER, STATE> boolean isNondeterministicInternal(STATE state, INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersInternal(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") final OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(state, letter)) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}
	
	
	public static <LETTER, STATE> boolean isNondeterministicCall(STATE state, INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersCall(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") final OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(state, letter)) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}
	
	public static <LETTER, STATE> boolean isNondeterministicReturnGivenHier(STATE state, STATE hier, INestedWordAutomaton<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersReturn(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") final OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessors(state, hier, letter)) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}
	
	public static <LETTER, STATE> boolean isNondeterministicReturn(STATE state, INestedWordAutomaton<LETTER, STATE> nwa) {
		for (final LETTER letter : nwa.lettersReturn(state)) {
			for (final STATE hier : nwa.hierPred(state, letter)) {
				int numberOfSuccs = 0;
				for (@SuppressWarnings("unused") final OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessors(state, hier, letter)) {
					numberOfSuccs++;
				}
				if (numberOfSuccs > 1) {
					return true;
				}
			}
		}
		return false;
	}
	
	
	@Override
	public Boolean getResult() {
		return mResult;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		final boolean correct = true;
		return correct;
	}
	
	
}

