package de.uni_freiburg.informatik.ultimate.automata.dynamic_stratified_reduction;

import java.util.HashSet;

/**
 * Used by DynamicStratifiedReduction to handle everything related to proofs
 * 
 *@param<S> 
 *	The type of states of the reduction automaton
 *@param<L>
 *	The type of letters of the reduction automaton
 *
 *@param<PROOF>
 *	The type of proofs
 */

public interface IProofManager<L, S, PROOF>{
	
	// Return true if a state is a proven state
	public boolean isProvenState(S state);
	
	
	// Chose a proof that is deemed responsible for state being a proven state
	public PROOF choseRespProof(S state); 


	
	// get all program variables used in the input proof
	public HashSet<L> getVariables(PROOF responsible);

}