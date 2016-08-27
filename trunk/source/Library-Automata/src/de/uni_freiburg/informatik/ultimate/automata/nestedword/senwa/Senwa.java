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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;

/**
 * Special case of NestedWordAutomaton in which we can partition the set of
 * states into modules. Each module has an unique entry state.
 * <ul>
 * <li> The entry state is the only state of a module which may have incoming
 * call transitions.
 * <li> The entry state is the only state of the module which may be an initial
 * state.
 * </ul>
 * ( I think 2012-09-17 the following should also apply:
 * Each entry state must be an initial state or has at least one incoming call
 * transition.)
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class Senwa<LETTER, STATE> extends DoubleDeckerAutomaton<LETTER, STATE> {
	
	private final Map<STATE,STATE> mState2Entry = new HashMap<STATE,STATE>();
	private final Map<STATE,Set<STATE>> mEntry2Module = new HashMap<STATE,Set<STATE>>();
	
	@Deprecated
	private final Map<STATE,Set<STATE>> mEntry2CallPredecessors = new HashMap<STATE,Set<STATE>>();

	/**
	 * @param services Ultimate services
	 * @param internalAlphabet internal alphabet
	 * @param callAlphabet call alphabet
	 * @param returnAlphabet return alphabet
	 * @param stateFactory state factory
	 */
	public Senwa(final AutomataLibraryServices services,
			final Set<LETTER> internalAlphabet,
			final Set<LETTER> callAlphabet, final Set<LETTER> returnAlphabet,
			final StateFactory<STATE> stateFactory) {
		super(services, internalAlphabet, callAlphabet, returnAlphabet, stateFactory);
		assert isModuleInformationConsistent();
	}
	
	
	/**
	 * @return true iff state is an entry state.
	 */
	public boolean isEntry(final STATE state) {
		return getEntry(state) == state;
	}
	
	
	/**
	 * @return The entry state of a given state.
	 */
	public STATE getEntry(final STATE state) {
		return mState2Entry.get(state);
	}
	

	/**
	 * @return The set of all states which have an outgoing call transition to
	 *     entry.
	 */
	public Set<STATE> getCallPredecessors(final STATE entry) {
		assert mEntry2Module.containsKey(entry);
		assert mEntry2CallPredecessors.containsKey(entry);
		return mEntry2CallPredecessors.get(entry);
	}
	
	/**
	 * Return all states <i>down</i> such that a configuration is reachable,
	 * where <i>up</i> is the current state and <i>down</i> is the topmost stack
	 * element.
	 */
	@Override
	public Set<STATE> getDownStates(final STATE up) {
		final STATE entry = getEntry(up);
		return getCallPredecessors(entry);
	}
	
	/**
	 * Returns true iff there is a reachable configuration in which the
	 * automaton is in STATE <i>up</i> and the STATE <i>down</i> is the topmost
	 * stack element.
	 */
	@Override
	public boolean isDoubleDecker(final STATE up, final STATE down) {
		final STATE entry = getEntry(up);
		if (entry == null) {
			return false;
		} else {
			final Set<STATE> downStates = getCallPredecessors(entry);
			return downStates.contains(down);
		}
	}
	
	
	/**
	 * @return The set of states s such that entry is the entry of s.
	 * 
	 */
	public Set<STATE> getModuleStates(final STATE entry) {
		assert mEntry2Module.containsKey(entry);
		return mEntry2Module.get(entry);
	}
	
	
	/**
	 * Don't use this for the construction of a Senwa.
	 */
	@Override
	public void addState(final boolean isInitial, final boolean isFinal, final STATE state) {
		throw new IllegalArgumentException("Specify entry");
	}

	public void addState(final STATE state, final boolean isInitial, final boolean isFinal,
																final STATE entry) {
		mState2Entry.put(state, entry);
		Set<STATE> module = mEntry2Module.get(entry);
		if (module == null) {
			assert state == entry;
			module = new HashSet<STATE>();
			mEntry2Module.put(entry, module);
		}
		module.add(state);
		super.addState(isInitial, isFinal, state);
		if (state == entry) {
			Set<STATE> callPreds = mEntry2CallPredecessors.get(state);
			if (callPreds == null) {
				callPreds = new HashSet<STATE>();
				mEntry2CallPredecessors.put(state, callPreds);
			}
			if (isInitial) {
				callPreds.add(super.getEmptyStackState());
			}
		}
		assert isModuleInformationConsistent();
	}

	@Override
	public void removeState(final STATE state) {
		final STATE entry = mState2Entry.get(state);
		assert entry != null;
		final Set<STATE> module = mEntry2Module.get(entry);
		final boolean success = module.remove(state);
		assert success : "State was not in module";
		
		for (final OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(state)) {
			final STATE succ = trans.getSucc();
			assert (isEntry(succ));
			final Set<STATE> callPreds = mEntry2CallPredecessors.get(succ);
			callPreds.remove(state);
		}
		
		if (isEntry(state)) {
			assert module.isEmpty() : "Can only delete entry if it was the last state in module";
			mEntry2Module.remove(state);
			mEntry2CallPredecessors.remove(state);
		}

		super.removeState(state);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
			final STATE predEntry = mState2Entry.get(pred);
			assert predEntry != null;
			final STATE succEntry = mState2Entry.get(succ);
			assert succEntry != null;
			if (predEntry != succEntry) {
				throw new IllegalArgumentException("Result is no senwa");
			}
		super.addInternalTransition(pred, letter, succ);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		final STATE succEntry = mState2Entry.get(succ);
		assert succ == succEntry;
		Set<STATE> callPreds = mEntry2CallPredecessors.get(succ);
		if (callPreds == null) {
			callPreds = new HashSet<STATE>();
			mEntry2CallPredecessors.put(succ, callPreds);
		}
		callPreds.add(pred);
		super.addCallTransition(pred, letter, succ);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addReturnTransition(final STATE pred, final STATE hier, final LETTER letter,
			final STATE succ) {
		final STATE predEntry = mState2Entry.get(pred);
		assert predEntry != null;
		final STATE hierEntry = mState2Entry.get(hier);
		assert hierEntry != null;
		final STATE succEntry = mState2Entry.get(succ);
		assert succEntry != null;
		assert hierEntry == succEntry;
		super.addReturnTransition(pred, hier, letter, succ);
		assert isModuleInformationConsistent();
	}
	
	
	public boolean isModuleInformationConsistent() {
		boolean result = true;
		
		for (final STATE state : getStates()) {
			final STATE entry = getEntry(state);
			if (entry == state) {
				result &= isEntry(state);
				assert result;
				for (final STATE callPred : getCallPredecessors(state)) {
					result &= (getStates().contains(callPred) || callPred == getEmptyStackState());
					assert result;
				}
			}
			final Set<STATE> module = getModuleStates(entry);
			result &= module.contains(state);
			assert result;
		}
		
		return result;
	}
	
	

}
