package local.stalin.automata.nwalibrary;

import java.util.Collection;

import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoRun;
import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoWord;

/**
 * Interface for nested word automata implementations.
 * 
 * Nested word automata are a machine model which accepts nested words which
 * have been introduced by Alur et al.
 * [1] http://www.cis.upenn.edu/~alur/nw.html
 * [2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13
 * [3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)
 * 
 * We use Objects as symbols of the alphabet. The type of these objects is 
 * specified by the Symbol parameter.
 * We allow to label states by Objects. The type of these objects is 
 * specified by the Content parameter.
 * 
 * We stick to the definitions of [2] and deviate from [3] by using only one
 * kind of states (not hierarchical states and linear states).
 * 
 * We also deviate form all common definitions of NWAs by specifying three Kinds
 * of Alphabets. The idea is that they do not have to be disjoint and allow to
 * totalize and complement the automaton with respect to this limitation of
 * which symbol can occur in which kind of transition (which is convenient to
 * speed up applications where the automaton models a program and call
 * statements occur anyway only at call transitions).
 * If you want to use NWAs according to the common definition just use the same
 * alphabet as internal, call and return alphabet. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <Symbol>
 * 		Type of the Objects which can be symbols of the alphabet.
 * @param <Content>
 * 		Type of Objects that are labeled to states. If you want to label your
 * 		states q0,q1...,qn you may choose String here. (But if, for example your
 * 		NWA represents a program and you want to label its states with
 * 		assertions you may choose Formula here)
 */

public interface INestedWordAutomaton<Symbol,Content> {
		
	public Collection<Symbol> getInternalAlphabet();
	public Collection<Symbol> getCallAlphabet();
	public Collection<Symbol> getReturnAlphabet();
	
	public Collection<IState<Symbol,Content>> getAllStates();
	public Collection<IState<Symbol,Content>> getInitialStates();
	public Collection<IState<Symbol,Content>> getFinalStates();
	public IState<Symbol,Content> getEmptyStackState();
	
	public IState<Symbol,Content> addState(boolean isInitial,
										   boolean isFinal,
										   Content content);

	
	/**
	 * Add a single internal transition from iState to succState.
	 * @param iState
	 * 		predecessor state
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' this transition
	 * @param succState
	 * 		successor state
	 */
	public void addInternalTransition(IState<Symbol, Content> iState,
									  Symbol symbol,
									  IState<Symbol, Content> succState);

	
	/**
	 * Add a set for internal transitions from iState to states in succStates
	 * @param iState
	 * 		predecessor state
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' this transition
	 * @param succStates
	 * 		successor states of the added transitions
	 */
	public void addInternalTransition(IState<Symbol, Content> iState,
									  Symbol symbol,
									  Collection<IState<Symbol, Content>> succStates);


	/**
	 * Add a single call transition from iState to succState.
	 * @param iState
	 * 		predecessor state
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' one of these transition
	 * @param succState
	 * 		successor state
	 */
	public void addCallTransition(IState<Symbol, Content> iState,
								  Symbol symbol,
								  IState<Symbol, Content> succState);
	

	/**
	 * Add a set for call transitions from iState to states in succStates
	 * @param iState
	 * 		predecessor state
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' this transition
	 * @param succStates
	 * 		successor states of the added transitions
	 */
	public void addCallTransition(IState<Symbol, Content> iState,
								  Symbol symbol,
								  Collection<IState<Symbol, Content>> succStates);
	
	
	/**
	 * Add a single return transition with hierarchical predecessor iState
	 * linear predecessor stateLinPred and successor succState.
	 * @param iState
	 * 		hierarchical predecessor
 	 * @param stateLinPred
 	 * 		linear predecessor
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' one this transition
	 * @param succState
	 * 		successor state
	 */
	public void addReturnTransition(IState<Symbol, Content> iState,
									IState<Symbol, Content> stateLinPred,
									Symbol symbol, IState<Symbol, Content> succState);
	/**
 	 * Add a set of return transitions with hierarchical predecessor iState
	 * linear predecessor stateLinPred and successor succState.
	 * @param iState
	 * 		hierarchical predecessor
	 * @param stateLinPred
	 * 		linear predecessor
	 * @param symbol
	 * 		symbol which is 'consumed' when 'taking' one of these transition
	 * @param succStates
	 * 		successor state
	 */
	public void addReturnTransition(IState<Symbol, Content> iState,
									IState<Symbol, Content> stateLinPred,
									Symbol symbol, Collection<IState<Symbol, Content>> succStates);
	
	public boolean isInitial(IState<Symbol,Content> state);
	
	public boolean isFinal(IState<Symbol,Content> state);
	
	public boolean accepts(NestedWord<Symbol> nw);
	
	public boolean accepts(NestedLassoWord<Symbol> nlw);
	
	
	/**
	 * language intersection of the automata
	 * @param nwa
	 * 		A nested word automaton.
	 * @return
	 * 		Nested word automaton that recognizes the intersection of the
	 * 		languages recognized by this automaton and the input nwa.
	 */
	public INestedWordAutomaton<Symbol,Content> intersect(INestedWordAutomaton<Symbol,Content> nwa);
	
	
	
	public INestedWordAutomaton<Symbol,Content> determinize();
	

	/**
	 * @return
	 * True, if for every state holds that
	 *  - for every symbol of the internal alphabet at most one successor is
	 *  		defined.
	 *  - for every symbol of the call alphabet at most one successor is 
	 *  		defined.
	 *  - for every symbol of the call alphabet and every linear predecessor
	 *  		state at most one successor is defined.
	 *  False otherwise.
	 *  Remark: A deterministic automaton may have several outgoing transitions
	 *  in a state labeled with the same symbol as long as the symbol occurs
	 *  only once per kind of transition. 
	 */
	public boolean isDeterministic();
	
	
	/**
	 * Transform this automaton to a nested word automaton that accepts the same
	 * language but is total, which means:
	 * For every state:
	 *  - for every symbol of the internal alphabet at least one successor is
	 *  		defined.
	 *  - for every symbol of the call alphabet at least one successor is 
	 *  		defined.
	 *  - for every symbol of the call alphabet and every linear predecessor
	 *  		state at least one successor is defined.
	 */
	public void totalize();
	
	
	/**
	 * Nested word automaton that accepts a nested word nw if nw is not accepted
	 * by this automaton and at every internal (resp. call, resp. return)
	 * position of nw is a symbol of the internal (resp. call, resp. return)
	 *  alphabet.
	 * @return
	 * 	Nested word automaton that accepts the complement of the language of
	 * 		this automaton with respect to the three alphabets. 
	 */
	public INestedWordAutomaton<Symbol,Content> complement();
	
	
	public ContentFactory<Content> getContentFactory();
	
	/**
	 * TODO comment
	 */
	public NestedLassoRun<Symbol,Content> getAcceptingNestedLassoRun();
	
	/**
	 * Emptiness check.
	 * @return An accepting NestedRun if there exists one, null otherwise.
	 */
	public NestedRun<Symbol,Content> getAcceptingNestedRun();
	
	
	/**
	 * TODO comment
	 */
	public INestedWordAutomaton<Symbol, Content> difference(
			INestedWordAutomaton<Symbol, Content> iNestedWordAutomaton);
}
