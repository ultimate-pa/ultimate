package local.stalin.automata.nwalibrary;

import java.util.Collection;

  /**
   * Interface for states of nested word automata implementations.
   * State objects represent not only the state itself, but also all outgoing
   * transitions.
   * @author heizmann@informatik.uni-freiburg.de
   * @param <Symbol>
   *	Type of the Objects which can be symbols of the alphabet.
   * @param <Content>
   * 	Type of Objects that are used to label states. (Details in the automaton
   * 	interface)
   */
public interface IState<Symbol,Content> {

	/**
	 * Returns the Object which labels this state and is of type Content
	 */
	public Content getContent();

	public boolean isFinal();
	
	
	/**
	 * Method to set this state to final/non-final.
	 * Used to allow an efficient negation operation. 
	 * 
	 * @param isFinal
	 * 		If true, this state becomes a final state. If false, this state
	 * 		becomes a non-final state.
	 */
	void setFinal(boolean isFinal);

	
	/**
	 * Returns all symbols that occur in outgoing internal transitions of this
	 * state. 
	 */
	public Collection<Symbol> getSymbolsInternal();
	
	
	/**
	 * Returns all symbols that occur in outgoing call transitions of this
	 * state. 
	 */
	public Collection<Symbol> getSymbolsCall();
	
	
	/**
	 * Returns all symbols that occur in outgoing return transitions of this
	 * state. 
	 */
	public Collection<Symbol> getSymbolsReturn();
	
	
	/**
	 * Returns the successors of all internal transitions labeled with symbol.
	 */
	public Collection<IState<Symbol,Content>> getInternalSucc(Symbol symbol);

	
	/**
	 * Returns the successors of all call transitions labeled with symbol.
	 */
	public Collection<IState<Symbol,Content>> getCallSucc(Symbol symbol);
	

	/**
	 * Returns all states that occur in an outgoing return transition labeled
	 * with symbol.
	 */
	public Collection<IState<Symbol,Content>> getReturnLinearPred(Symbol symbol);
	
	
	/**
	 * Returns the successors of all return transitions whose linear predecessor
	 * is stateLinPrad and which are labeled with symbol.
	 */
	public Collection<IState<Symbol,Content>> getReturnSucc(IState<Symbol,Content> stateLinPred, Symbol symbol);

/* Better not make this public -- why is package private not possible?
	void addInternalTransition(Symbol symbol, Collection<IState<Symbol, Content>> successors);
	void addCallTransition(Symbol symbol, Collection<IState<Symbol, Content>> successors);
	void addReturnTransition(Symbol symbol, IState<Symbol, Content> linearPred, Collection<IState<Symbol, Content>> successors);
*/
	
	public int internalTransitions();
	
	public int callTransitions();
	
	public int returnTransitions();
	
}
