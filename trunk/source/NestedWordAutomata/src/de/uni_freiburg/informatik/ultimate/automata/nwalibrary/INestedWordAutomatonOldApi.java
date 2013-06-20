package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;



public interface INestedWordAutomatonOldApi<LETTER,STATE> 
										extends IAutomaton<LETTER,STATE>, INestedWordAutomaton<LETTER, STATE> {


	
	/**
	 * Returns the set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly.
	 */
	public Collection<STATE> getStates();
	
	/**
	 * Returns the set of initial states. 
	 */
	public Collection<STATE> getInitialStates();
	
	
	/**
	 * Returns the set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly. Use the
	 * {@link isFinal} method to check if a specific state is final. 	
	 */
	public Collection<STATE> getFinalStates();


	
	


	/**
	 * @return All letters a such that state has an incoming internal 
	 * transition labeled with letter a.
	 */
	public Set<LETTER> lettersInternalIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming call 
	 * transition labeled with letter a.
	 */	
	public Set<LETTER> lettersCallIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming return 
	 * transition labeled with letter a.
	 */		
	public Set<LETTER> lettersReturnIncoming(STATE state);
	
	/**
	 * @return All letters a such that state occurs as hierarchical predecessor
	 * in a return transition labeled with letter a.
	 */
	public Set<LETTER> lettersReturnSummary(STATE state);

	

	/**
	 * @return All states succ such that state has an outgoing 
	 * internal transition (state, letter, succ)
	 */
	public Iterable<STATE> succInternal(STATE state, LETTER letter);
	
	/**
	 * @return All states succ such that state has an outgoing 
	 * call transition (state, letter, succ)
	 */
	public Iterable<STATE> succCall(STATE state, LETTER letter);
	
	
	
	/**
	 * @return All states succ such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter);

	/**
	 * @return All states pred such that there is an incoming 
	 * internal transition (pred, letter, state)
	 */
	public Iterable<STATE> predInternal(STATE state, LETTER letter);

	/**
	 * @return All states pred such that there is an incoming 
	 * call transition (pred, letter, state)
	 */
	public Iterable<STATE> predCall(STATE state, LETTER letter);
	
	
	/**
	 * @return All states pred such that there is an incoming 
	 * return transition (pred, hier, letter, state)
	 */
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier);

	/**
	 * @return All states hier such that there is a state pred such that there 
	 * is an incoming return transition (pred, hier, letter, state)
	 */
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter);
	
	
	
	
	/**
	 * Return true iff we can not leave the set of final states, i.e.,
	 * if q is final and there is a transitions (q,a,q') then q' is final.
	 * Not important. Only used to check correctness of one operation. Might
	 * be moved to this operation.
	 * 
	 */
	public boolean finalIsTrap();
	

	/**
	 * Return true iff there is at most one initial state and for each state q
	 * of the automaton the following holds
	 * <ul>
	 * <li> for each letter a of the internal alphabet there is at most one
	 * transition (q,a,q').
	 * <li> for each letter a of the call alphabet there is at most one
	 * transition (q,a,q').
	 * <li> for each letter a of the return alphabet and each state q̀ of the 
	 * automaton there is at most one transition (q,q̀,a,q').
	 * </ul>
	 */
	public boolean isDeterministic();
	
	
	/**
	 * @return true iff there is at least one initial state and for each state
	 * q and each letter a 
	 * <ul>
	 *  <li> q has an outgoing internal transition labeled with a.
	 *  <li> q has an outgoing call transition labeled with a.
	 *  <li> q has an outgoing return transition labeled with a.
	 * </ul>
	 */
	boolean isTotal();
	
	
}
