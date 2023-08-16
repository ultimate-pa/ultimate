package de.uni_freiburg.informatik.ultimate.automata.dynamic_stratified_reduction;

import java.util.HashSet;


/**
 * Used by DynamicStratifiedReduction to handle everything related to proofs
 * 
 *@param<S> 
 *	The type of state of the reduction automaton
 *@param<L>
 *	The type of letter of the reduction automaton
 *
 *@param<PROOF>
 *	Placeholder since idk in what form the proofs are given/can be accessed
 */

public class ProofManager<L, S, PROOF> {
	private int[] proofCounter; 	// count how many times each proof has been chosen as responsible
	private PROOF lastResp;	// the proof we chose at the last proven state
	
	public ProofManager(int numProofs){
		proofCounter = new int[numProofs];
		lastResp = null;
	}
	
	public boolean isProvenState(S state){
	// TODO implement this 
	// Identify if a state is a proven state
		return false;
	}
	
	public PROOF choseRespProof(S state) {
	// TODO implement this
	// Chose a proof that is deemed responsible for state being a proven state
	/*
	 * Priorities:
	 * (1) last chosen proof
	 * (2) number of times chosen (asc.)
	 * (3) refinement round the proof was found in (desc.)
	 * 
	 */
		return null;
	}
	
	public HashSet<L> getVariables(PROOF responsible){
	//TODO implement this
	// get all program variables used in the input proof
		return null;
	}

}
