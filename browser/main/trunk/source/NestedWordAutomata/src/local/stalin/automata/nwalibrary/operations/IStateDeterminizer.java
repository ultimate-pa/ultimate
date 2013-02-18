package local.stalin.automata.nwalibrary.operations;


public interface IStateDeterminizer<S,C> {
	
	/**
	 * Given a DeterminizedState detState, return the successor state under an
	 * internal transition labeled with symbol.
	 */
	DeterminizedState<S,C> internalSuccessor(DeterminizedState<S,C> detState,
											 S symbol);

	
	/**
	 * Compute successor detState under call transition of a detState
	 * and symbol. 
	 */
	DeterminizedState<S,C> callSuccessor(DeterminizedState<S,C> detState, 
										 S symbol);

	
	/**
	 * Given a DeterminizedState detState, return the successor state under a
	 * return transition for linear predecessor linPred labeled with symbol.
	 */
	DeterminizedState<S,C> returnSuccessor(DeterminizedState<S,C> detState,
										   DeterminizedState<S,C> linPred,
										   S symbol);
	
}