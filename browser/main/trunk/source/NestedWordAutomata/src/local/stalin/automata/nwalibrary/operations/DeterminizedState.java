package local.stalin.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.Pair;

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
 * @param <S> Symbol
 * @param <C> Content
 */
public class DeterminizedState<S,C> {
	
	/**
	 * Set of ordered pairs. The pair (present,caller) is in this set iff 
	 * present is contained in the image of caller.  
	 */
	private final Map<IState<S,C>,Set<IState<S,C>>> caller2presents;
	
	private final ContentFactory<C> contentFactory;
	private boolean isFinal = false;
	
	public DeterminizedState(ContentFactory<C> cdF) {
		caller2presents = new HashMap<IState<S,C>, Set<IState<S,C>>>();
		contentFactory = cdF;
	}
	
	
	
	public Set<IState<S, C>> getCallerStates() {
		return caller2presents.keySet();
	}
	
	
	public Set<IState<S,C>> getPresentStates(IState<S,C> caller) {
		return caller2presents.get(caller);
	}
	

	/**
	 * @return true iff for some pair in the set, the first entry is an
	 * accepting state.
	 */
	boolean isFinal() {
		return isFinal;
	}
	
//	boolean isEmpty() {
//		return pairList.keySet().isEmpty();
//	}
	

	/**
	 * By the contentFactory created content for the determinized state.
	 */
	public C getContent() {
		Collection<Pair<C,C>> cPairList = new LinkedList<Pair<C,C>>();
		for (IState<S,C> caller : caller2presents.keySet()) {
			for (IState<S,C> present : caller2presents.get(caller)) {
				Pair<C,C> pair = new Pair<C,C>(caller.getContent(),
														present.getContent());
				cPairList.add(pair);
			}
		}
		
		C result = contentFactory.createContentOnDeterminization(cPairList);
//		assert (result != null);
		return result;
	}


	/**
	 * Add the pair (caller,present) to the set. 
	 */
	public void addPair(IState<S,C> caller, IState<S,C> present) {
		if (present.isFinal()) {
			isFinal = true;
		}
		Set<IState<S,C>> presentStates = caller2presents.get(caller);
		if (presentStates == null) {
			presentStates = new HashSet<IState<S,C>>();
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
			DeterminizedState<S,C> detState = (DeterminizedState<S,C>) obj;
			return caller2presents.equals(detState.caller2presents);
		}
		else {
			return false;
		}
	}
	
	
	@Override
	public int hashCode() {
		return caller2presents.hashCode();
	}
	

	public String toString() {
		return caller2presents.toString();
	}		
}
