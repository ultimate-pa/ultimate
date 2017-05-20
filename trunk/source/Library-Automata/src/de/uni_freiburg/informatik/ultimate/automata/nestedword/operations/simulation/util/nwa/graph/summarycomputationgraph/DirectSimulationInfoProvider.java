/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;

/**
 * Provide information about direct simulation that is needed for constructing the game graph and for obtaining
 * simulation results.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DirectSimulationInfoProvider<LETTER, STATE> implements ISimulationInfoProvider<LETTER, STATE> {

	@Override
	public boolean computeBitForInitialVertex(final boolean isSpoilerAccepting, final boolean isDuplicatorAccepting) {
		return false;
	}

	@Override
	public boolean computeBitForSpoilerVertex(final boolean predecessorBit, final boolean isSpoilerAccepting) {
		return false;
	}

	@Override
	public boolean computeBitForDuplicatorVertex(final boolean predecessorBit, final boolean isDuplicatorAccepting) {
		return false;
	}

	@Override
	public int computePriority(final boolean bit, final boolean isSpoilerAccepting,
			final boolean isDuplicatorAccepting) {
		return 2;
	}

	@Override
	public boolean isImmediatelyWinningForSpoiler(final boolean isSpoilerAccepting,
			final boolean isDuplicatorAccepting) {
		return isSpoilerAccepting && !isDuplicatorAccepting;
	}

	@Override
	public boolean isSimulationInformationProvider(final SpoilerVertex<LETTER, STATE> spoilerVertex,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> inputAutomaton) {
		if (spoilerVertex.getQ0() == null || spoilerVertex.getQ1() == null) {
			throw new UnsupportedOperationException("no states are not supported");
		}
		if (spoilerVertex.isB()) {
			throw new UnsupportedOperationException("no b in direct simulation");
		}
		return true;
	}

	@Override
	public boolean mayMergeFinalAndNonFinalStates() {
		return false;
	}

}
