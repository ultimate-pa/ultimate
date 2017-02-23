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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.GameAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.GameCallReturnSummary;

/**
 * TODO
 * 
 * @author 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SpoilerSubSummaryPriorityVertex<LETTER, STATE> extends SpoilerVertex<LETTER, STATE> {

	private final GameCallReturnSummary<STATE> mSummary;
	private final IGameState mSubSummaryTarget;

	public SpoilerSubSummaryPriorityVertex(final GameCallReturnSummary<STATE> summary,
			final IGameState subSummaryTarget) {
		super(summary.getDuplicatorResponses().get(subSummaryTarget),
				GameAutomaton.unwrapSpoilerNwaVertex(summary.getSummarySource()).isB(), null, null);
		mSummary = summary;
		mSubSummaryTarget = subSummaryTarget;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((mSubSummaryTarget == null) ? 0 : mSubSummaryTarget.hashCode());
		result = prime * result + ((mSummary == null) ? 0 : mSummary.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		final SpoilerSubSummaryPriorityVertex other = (SpoilerSubSummaryPriorityVertex) obj;
		if (mSubSummaryTarget == null) {
			if (other.mSubSummaryTarget != null)
				return false;
		} else if (!mSubSummaryTarget.equals(other.mSubSummaryTarget))
			return false;
		if (mSummary == null) {
			if (other.mSummary != null)
				return false;
		} else if (!mSummary.equals(other.mSummary))
			return false;
		return true;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "SpoilerSubSummaryPriorityVertex [mSummary=" + mSummary + ", mSubSummaryTarget=" + mSubSummaryTarget
				+ "]";
	}

}
