package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * Determinized state in the classical determinization algorithm for NWAs.
 * While determinizing a nondeterministic finite automaton NFA using the
 * powerset construction a state in the determinized automaton corresponds to a
 * subset of the states of A.
 * For NWAs there exists a similar construction. Let A be a nondeterministic
 * NWA. A state in the determinized NWA corresponds to a set of ordered pairs
 * of A's states. In such a pair, the first state (present) represents a
 * state "in which A can be at the moment", the second state (caller)
 * represents the state "before the last call statement", i.e. the second state
 * represents "the top of the stack".
 * 
 * @param <LETTER> Symbol
 * @param <STATE> Content
 */
public class DeterminizedState<LETTER,STATE> {
	
	/**
	 * Set of ordered pairs. The pair (present,caller) is in this set iff 
	 * present is contained in the image of caller.  
	 */
	private final Map<STATE,Set<STATE>> caller2presents;
	private boolean m_ConstructionFinished;
	private int m_HashCode;
	private boolean containsFinal = false;
	private STATE m_CachedResultingState = null;
	
	public DeterminizedState(INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		caller2presents = new HashMap<STATE,Set<STATE>>();
	}
	
	public Set<STATE> getDownStates() {
		return caller2presents.keySet();
	}
	
	
	public Set<STATE> getUpStates(STATE caller) {
		return caller2presents.get(caller);
	}
	

	/**
	 * @return true iff for some pair in the set, the first entry is an
	 * accepting state.
	 */
	public boolean containsFinal() {
		return containsFinal;
	}
	
	/**
	 * @return true iff for all pair in the set, the first entry is an
	 * accepting state and the set is not empty
	 */
	public boolean allFinal(INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		if (caller2presents.isEmpty()) {
			return false;
		}
		for (STATE down : caller2presents.keySet()) {
			for (STATE up : caller2presents.get(down)) {
				if (!nwa.isFinal(up)) {
					return false;
				}
			}
		}
		return true;
	}
	

	/**
	 * By the contentFactory created content for the determinized state.
	 */
	public STATE getContent(StateFactory<STATE> stateFactory) {
		if (m_CachedResultingState == null) {
			m_CachedResultingState = stateFactory.determinize(caller2presents);
		}
		return m_CachedResultingState;
	}


	/**
	 * Add the pair (caller,present) to the set. 
	 */
	public void addPair(STATE caller, STATE present, INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		if (m_ConstructionFinished) {
			throw new IllegalArgumentException("Construction finished must not add pairs.");
		}
		if (nwa.isFinal(present)) {
			containsFinal = true;
		}
		Set<STATE> presentStates = caller2presents.get(caller);
		if (presentStates == null) {
			presentStates = new HashSet<STATE>();
			caller2presents.put(caller, presentStates);
		}
		presentStates.add(present);
	}
	
	
	/**
	 * Two DeterminizedStates are equivalent iff they represent the same set of
	 * state pairs. 
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof DeterminizedState) {
			DeterminizedState<LETTER,STATE> detState = (DeterminizedState<LETTER,STATE>) obj;
			return caller2presents.equals(detState.caller2presents);
		}
		else {
			return false;
		}
	}
	
	
	@Override
	public int hashCode() {
		if (!m_ConstructionFinished) {
			m_HashCode = caller2presents.hashCode();
			m_ConstructionFinished = true;
		}
		return m_HashCode;
	}
	

	public String toString() {
		return caller2presents.toString();
	}
	
	public boolean isSubsetOf(DeterminizedState<LETTER,STATE> superset) {
		for (STATE down : getDownStates()) {
			Set<STATE> SupersetUpStates = superset.getUpStates(down);
			if (SupersetUpStates == null) {
				return false;
			}
			else {
				for (STATE up : getUpStates(down)) {
					if (!SupersetUpStates.contains(up)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	public boolean isEmpty() {
		return caller2presents.isEmpty();
	}
	
	public int degreeOfNondeterminism() {
		int degree = 0;
		for ( STATE down : getDownStates()) {
			degree += getUpStates(down).size();
		}
		return degree;
	}
}
