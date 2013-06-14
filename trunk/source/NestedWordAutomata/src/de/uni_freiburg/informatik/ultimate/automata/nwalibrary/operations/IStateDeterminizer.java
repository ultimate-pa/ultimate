package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;


public interface IStateDeterminizer<LETTER,STATE> {
	
	DeterminizedState<LETTER,STATE> initialState();
	
	/**
	 * Given a DeterminizedState detState, return the successor state under an
	 * internal transition labeled with symbol.
	 */
	DeterminizedState<LETTER,STATE> internalSuccessor(DeterminizedState<LETTER,STATE> detState,
											 LETTER symbol);

	
	/**
	 * Compute successor detState under call transition of a detState
	 * and symbol. 
	 */
	DeterminizedState<LETTER,STATE> callSuccessor(DeterminizedState<LETTER,STATE> detState, 
										 LETTER symbol);

	
	/**
	 * Given a DeterminizedState detState, return the successor state under a
	 * return transition for linear predecessor linPred labeled with symbol.
	 */
	DeterminizedState<LETTER,STATE> returnSuccessor(DeterminizedState<LETTER,STATE> detState,
										   DeterminizedState<LETTER,STATE> linPred,
										   LETTER symbol);

	int getMaxDegreeOfNondeterminism();
	
	/**
	 * If true, the constructed DeterminizedStates are sets of DoubleDecker,
	 * needed, e.g. for exact determinization of nested word automata.
	 * If false, the constructed DeterminziedStates are sets of States. This
	 * is sufficient for exact determinization of finite automata. We also use
	 * these DeterminziedStates for determinizations where the resulting
	 * automaton recognizes a superset of the input automatons language.
	 */
	boolean useDoubleDeckers();
	
}