package local.stalin.automata.nwalibrary;

import java.util.Collection;

public interface IStateDl<Symbol, Content> extends IState<Symbol, Content> {
	
	/**
	 * Returns all symbols that occur in internal call transitions of this
	 * state. 
	 */
	public Collection<Symbol> getInSymbolsCall();
	
	
	/**
	 * Returns all symbols that occur in internal internal transitions of this
	 * state. 
	 */
	public Collection<Symbol> getInSymbolsInternal();
	
		
	/**
	 * Returns all symbols that occur in internal return transitions of this
	 * state. 
	 */
	public Collection<Symbol> getInSymbolsReturn();

	/**
	 * Returns all states that have a incoming return transition whose linear
	 * predecessor state is this state.
	 */
	public Collection<IStateDl<Symbol,Content>> getSummaryCandidates();
	
	
	/**
	 * Returns the predecessors of all call transitions labeled with symbol.
	 */
	public Collection<IStateDl<Symbol,Content>> getInCall(Symbol symbol);

	
	/**
	 * Returns the predecessors of all internal transitions labeled with symbol.
	 */
	public Collection<IStateDl<Symbol,Content>> getInInternal(Symbol symbol);


	/**
	 * Returns the hierarchical predecessors of all return transitions labeled
	 * with symbol.
	 */
	public Collection<IStateDl<Symbol,Content>> getInReturnHierarc(Symbol symbol);

	
	/**
	 * Returns the linear predecessors of all return transitions labeled with
	 * symbol.
	 */
	public Collection<IStateDl<Symbol,Content>> getInReturnLinear(Symbol symbol);
	
	
	/**
	 * Returns for each return transition that has this state as linear
	 * predecessor and summaryCandidate as successor the symbol of this return
	 *  transition.
	 */
	public Collection<Symbol> 
		getSummaryCandidateSymbol(IStateDl<Symbol,Content> summaryCandidate);
}
