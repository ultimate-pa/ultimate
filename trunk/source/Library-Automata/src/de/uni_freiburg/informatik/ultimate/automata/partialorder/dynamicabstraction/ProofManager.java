/*
 * Copyright (C) 2023 Veronika Klasen
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

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

public class ProofManager<H, S, PROOF> {
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

	public H getVariables(final PROOF responsible) {
		// TODO implement this
		// get all program variables used in the input proof
		return null;
	}

}
