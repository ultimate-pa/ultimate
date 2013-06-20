package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
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
public interface INestedWordAutomatonSimple<LETTER, STATE> extends IAutomaton<LETTER, STATE> {
	
	/**
	 * Set of all letters that can occur as label of an internal transition. 
	 * The default definition of nested word automata does not allow separate
	 * alphabets for internal, call and return. The default definition of 
	 * visibly pushdown automata requires that all three alphabets are disjoint.
	 * We deviate from both definitions. We allow separate alphabets but do not
	 * require that they are disjoint.
	 */
	public Set<LETTER> getInternalAlphabet();


	/**
	 * Set of all letters that can occur as label of a call transition. 
	 * The default definition of nested word automata does not allow separate
	 * alphabets for internal, call and return. The default definition of 
	 * visibly pushdown automata requires that all three alphabets are disjoint.
	 * We deviate from both definitions. We allow separate alphabets but do not
	 * require that they are disjoint.
	 */
	public Set<LETTER> getCallAlphabet();


	/**
	 * Set of all letters that can occur as label of a return transition. 
	 * The default definition of nested word automata does not allow separate
	 * alphabets for internal, call and return. The default definition of 
	 * visibly pushdown automata requires that all three alphabets are disjoint.
	 * We deviate from both definitions. We allow separate alphabets but do not
	 * require that they are disjoint.
	 */
	public Set<LETTER> getReturnAlphabet();
	
	
	/**
	 * @return The StateFactory which was used to construct the states of this
	 * automaton.
	 */
	public StateFactory<STATE> getStateFactory();
	
	
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
	 * All initial states of automaton. 
	 */
	public abstract Iterable<STATE> getInitialStates();
	
	/**
	 * Returns true iff state is initial.
	 */
	public boolean isInitial(STATE state);
	
	
	/**
	 * Returns true iff state is final.
	 */
	public boolean isFinal(STATE state);

	/**
	 * Superset of all letters a such that state has an outgoing internal 
	 * transition labeled with letter a.
	 */
	public Set<LETTER> lettersInternal(STATE state);
	
	/**
	 * Superset of all letters a such that state has an outgoing call 
	 * transition labeled with letter a.
	 */	
	public Set<LETTER> lettersCall(STATE state);
	
	/**
	 * Superset of all letters a such that state has an outgoing return 
	 * transition labeled with letter a.
	 */		
	public Set<LETTER> lettersReturn(STATE state);

	
	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			final STATE state, final STATE hier, final LETTER letter);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier);
}
