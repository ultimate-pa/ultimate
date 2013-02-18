package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

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
 */
public class Senwa<LETTER, STATE> extends DoubleDeckerAutomaton<LETTER, STATE> {
	
	
	Map<STATE,STATE> m_State2Entry = new HashMap<STATE,STATE>();
	Map<STATE,Set<STATE>> m_Entry2Module = new HashMap<STATE,Set<STATE>>();
	
	@Deprecated
	Map<STATE,Set<STATE>> m_Entry2CallPredecessors = new HashMap<STATE,Set<STATE>>();

	public Senwa(Collection<LETTER> internalAlphabet,
			Collection<LETTER> callAlphabet, Collection<LETTER> returnAlphabet,
			StateFactory<STATE> stateFactory) {
		super(internalAlphabet, callAlphabet, returnAlphabet, stateFactory);
		assert isModuleInformationConsistent();
	}
	
	
	/**
	 * Returns true iff state is an entry state.
	 */
	public boolean isEntry(STATE state) {
		return getEntry(state) == state;
	}
	
	
	/**
	 * Returns the entry state of a given state.
	 */
	public STATE getEntry(STATE state) {
		return m_State2Entry.get(state);
	}
	

	/**
	 * Return the set of all states which have an outgoing call transition to
	 * entry.
	 */
	public Set<STATE> getCallPredecessors(STATE entry) {
		assert m_Entry2Module.containsKey(entry);
		assert m_Entry2CallPredecessors.containsKey(entry);
		return m_Entry2CallPredecessors.get(entry);
	}
	
	/**
	 * Return all states <i>down</i> such that a configuration is reachable,
	 * where <i>up</i> is the current state and <i>down</i> is the topmost stack
	 * element.
	 */
	public Set<STATE> getDownStates(STATE up) {
		STATE entry = getEntry(up);
		return getCallPredecessors(entry);
	}
	
	/**
	 * Returns true iff there is a reachable configuration in which the 
	 * automaton is in STATE <i>up</i> and the STATE <i>down</i> is the topmost
	 * stack element.
	 */
	public boolean isDoubleDecker(STATE up, STATE down) {
		STATE entry = getEntry(up);
		if (entry == null) {
			return false;
		} else {
			Set<STATE> downStates = getCallPredecessors(entry);
			return downStates.contains(down);
		}
	}
	
	
	/**
	 * Return the set of states s such that entry is the entry of s. 
	 * 
	 */
	public Set<STATE> getModuleStates(STATE entry) {
		assert m_Entry2Module.containsKey(entry);
		return m_Entry2Module.get(entry);
	}
	
	
	/**
	 * Don't use this for the construction of a Senwa. 
	 */
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		throw new IllegalArgumentException("Specify entry");
	}

	public void addState(STATE state, boolean isInitial, boolean isFinal, 
																STATE entry) {
		m_State2Entry.put(state, entry);
		Set<STATE> module = m_Entry2Module.get(entry);
		if (module == null) {
			assert state == entry;
			module = new HashSet<STATE>();
			m_Entry2Module.put(entry, module);
		}
		module.add(state);
		super.addState(isInitial, isFinal, state);
		if (state == entry) {
			Set<STATE> callPreds = m_Entry2CallPredecessors.get(state);
			if (callPreds == null) {
				callPreds = new HashSet<STATE>();
				m_Entry2CallPredecessors.put(state, callPreds);
			}
			if (isInitial) {
				callPreds.add(super.getEmptyStackState());
			}
		}
		assert isModuleInformationConsistent();
	}

	@Override
	public void removeState(STATE state) {
		STATE entry = m_State2Entry.get(state);
		assert entry != null;
		Set<STATE> module = m_Entry2Module.get(entry);
		boolean success = module.remove(state);
		assert success : "State was not in module";
		
		for (LETTER letter : lettersCall(state)) {
			for (STATE succ : succCall(state, letter)) {
				assert (isEntry(succ));
				Set<STATE> callPreds = m_Entry2CallPredecessors.get(succ);
				callPreds.remove(state);
			}
		}
		
		if (isEntry(state)) {
			assert module.size() == 0 : "Can only delete entry if it was the last state in module";
			m_Entry2Module.remove(state);
			m_Entry2CallPredecessors.remove(state);
		}

		super.removeState(state);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
			STATE predEntry = m_State2Entry.get(pred);
			assert predEntry != null;
			STATE succEntry = m_State2Entry.get(succ);
			assert succEntry != null;
			if( predEntry != succEntry) {
				throw new IllegalArgumentException("Result is no senwa");
			}
		super.addInternalTransition(pred, letter, succ);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		STATE succEntry = m_State2Entry.get(succ);
		assert succ == succEntry;
		Set<STATE> callPreds = m_Entry2CallPredecessors.get(succ);
		if (callPreds == null) {
			callPreds = new HashSet<STATE>();
			m_Entry2CallPredecessors.put(succ, callPreds);
		}
		callPreds.add(pred);
		super.addCallTransition(pred, letter, succ);
		assert isModuleInformationConsistent();
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		STATE predEntry = m_State2Entry.get(pred);
		assert predEntry != null;
		STATE hierEntry = m_State2Entry.get(hier);
		assert hierEntry != null;
		STATE succEntry = m_State2Entry.get(succ);
		assert succEntry != null;
		assert hierEntry == succEntry;
		super.addReturnTransition(pred, hier, letter, succ);
		assert isModuleInformationConsistent();
	}
	
	
	public boolean isModuleInformationConsistent() {
		boolean result = true;
		
		for (STATE state : getStates()) {
			STATE entry = getEntry(state);
			if (entry == state) {
				result &= isEntry(state);
				assert result;
				for (STATE callPred : getCallPredecessors(state)) {
					result &= (getStates().contains(callPred) || callPred == getEmptyStackState());
					assert result;
				}
			}
			Set<STATE> module = getModuleStates(entry);
			result &= module.contains(state);
			assert result;
		}
		
		return result;
	}
	
	

}
