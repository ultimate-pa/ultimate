package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;

/**
 * Interface for nested word automata implementations.
 * 
 * Nested word automata are a machine model which accepts nested words which
 * have been introduced by Alur et al.
 * [1] http://www.cis.upenn.edu/~alur/nw.html
 * [2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13
 * [3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)
 * 
 * We stick to the definitions of [2] and deviate from [3] by using only one
 * kind of states (not hierarchical states and linear states).
 * 
 * We also deviate form all common definitions of NWAs by specifying three Kinds
 * of Alphabets. The idea is that they do not have to be disjoint and allow to
 * totalize and complement the automaton with respect to this limitation of
 * which letter can occur in which kind of transition (which is convenient to
 * speed up applications where the automaton models a program and call
 * statements occur anyway only at call transitions).
 * If you want to use NWAs according to the common definition just use the same
 * alphabet as internal, call and return alphabet. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * 		Type of Objects which can be used as letters of the alphabet.
 * @param <STATE>
 *		Type of Objects which can be used as states.
 */

public interface INestedWordAutomaton<LETTER,STATE> 
										extends IAutomaton<LETTER,STATE> {
	/**
	 * Letters allowed at internal positions of nested words accepted by this
	 * automaton. If you use an nested word automaton as finite automaton this
	 * is you alphabet Σ.
	 */
	public Collection<LETTER> getInternalAlphabet();
	public Collection<LETTER> getCallAlphabet();
	public Collection<LETTER> getReturnAlphabet();
	
	/**
	 * @return The StateFactory which was used to construct the states of this
	 * automaton.
	 */
	public StateFactory<STATE> getStateFactory();
	
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
	 * Returns true iff state is initial.
	 */
	public boolean isInitial(STATE state);
	
	
	/**
	 * Returns true iff state is final.
	 */
	public boolean isFinal(STATE state);
	
	

	public void addState(boolean isInitial, boolean isFinal, STATE state);

	
	/**
	 * Remove state and all its incoming and outgoing transitions. 
	 */
	void removeState(STATE state);
	
	
	/**
	 * Auxiliary state used to model the hierarchical predecessor of a pending
	 * return in some operations. Recall that we generally do not accept nested
	 * word with pending returns. This auxiliary state is <i>never</i> contained
	 * is the set of states.
	 * Viewing nested word automata as visibly pushdown automata this state can
	 * be seen as a "bottom letter" of the pushdown alphabet.
	 */
	public STATE getEmptyStackState();


	/**
	 * @return All letters a such that state has an outgoing internal 
	 * transition labeled with letter a.
	 */
	public Collection<LETTER> lettersInternal(STATE state);
	
	/**
	 * @return All letters a such that state has an outgoing call 
	 * transition labeled with letter a.
	 */	
	public Collection<LETTER> lettersCall(STATE state);
	
	/**
	 * @return All letters a such that state has an outgoing return 
	 * transition labeled with letter a.
	 */		
	public Collection<LETTER> lettersReturn(STATE state);



	
	/**
	 * @return All letters a such that state has an incoming internal 
	 * transition labeled with letter a.
	 */
	public Collection<LETTER> lettersInternalIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming call 
	 * transition labeled with letter a.
	 */	
	public Collection<LETTER> lettersCallIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming return 
	 * transition labeled with letter a.
	 */		
	public Collection<LETTER> lettersReturnIncoming(STATE state);
	
	/**
	 * @return All letters a such that state occurs as hierarchical predecessor
	 * in a return transition labeled with letter a.
	 */
	public Collection<LETTER> lettersReturnSummary(STATE state);

	

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
	 * @return All states hier such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	public Iterable<STATE> hierPred(STATE state, LETTER letter);		
	
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
	 * Add internal transition (pred, letter, succ) to automaton.
	 */
	void addInternalTransition(STATE pred, LETTER letter, STATE succ);
	
	/**
	 * Add call transition (pred, letter, succ) to automaton.
	 */	
	void addCallTransition(STATE pred, LETTER letter, STATE succ);

	/**
	 * Add return transition (pred, hier, letter, succ) to automaton.
	 * State pred is called linear predecessor.
	 * State hier is called hierarchical predecessor.
	 */	
	void addReturnTransition(STATE pred, STATE hier, LETTER letter, STATE succ);	
	
	

	
	
	
	
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
	
	

	
	
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier);

	


}
