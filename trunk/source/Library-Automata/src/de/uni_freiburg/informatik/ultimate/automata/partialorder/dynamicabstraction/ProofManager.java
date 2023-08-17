package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import java.util.HashSet;

/**
 * Used by DynamicStratifiedReduction to handle everything related to proofs
 *
 * @param<S> The
 *               type of state of the reduction automaton
 * @param<L> The
 *               type of letter of the reduction automaton
 *
 * @param<PROOF> Placeholder
 *                   since idk in what form the proofs are given/can be accessed
 */

public class ProofManager<L, S, PROOF> {
	private final int[] proofCounter; // count how many times each proof has been chosen as responsible
	private final PROOF lastResp; // the proof we chose at the last proven state

	public ProofManager(final int numProofs) {
		proofCounter = new int[numProofs];
		lastResp = null;
	}

	public boolean isProvenState(final S state) {
		// TODO implement this
		// Identify if a state is a proven state
		return false;
	}

	public PROOF choseRespProof(final S state) {
		// TODO implement this
		// Chose a proof that is deemed responsible for state being a proven state
		/*
		 * Priorities: (1) last chosen proof (2) number of times chosen (asc.) (3) refinement round the proof was found
		 * in (desc.)
		 *
		 */
		return null;
	}

	public HashSet<L> getVariables(final PROOF responsible) {
		// TODO implement this
		// get all program variables used in the input proof
		return null;
	}

}
