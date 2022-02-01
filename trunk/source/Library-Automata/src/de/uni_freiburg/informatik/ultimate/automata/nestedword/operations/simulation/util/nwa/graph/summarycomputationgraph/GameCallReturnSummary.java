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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;

/**
 * Objects of this class represent several sequences of moves in a two player game on an automaton whose states have
 * type STATE. Here we presume that the game graph is given as a game automaton whose states are {@link IGameState}s.
 * The sequences of moves that we can represent all start in mSummarySource. The sequences of moves that we can
 * represent all end in an IGameState whose spoiler component is mSpoilerDestinationState. The sequences of moves that
 * we can represent all end the key set of mDuplicatorResponses. The corresponding value of this keys denote the
 * priority that all these sequences have. (priority of sequence == lowest priority among all spoiler nodesin sequence)
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class GameCallReturnSummary<STATE> {
	private final IGameState mSummarySource;
	private final STATE mSpoilerDestinationState;
	private final Map<IGameState, Integer> mDuplicatorResponses;

	public GameCallReturnSummary(final IGameState summarySource, final STATE spoilerDestinationState,
			final Map<IGameState, Integer> duplicatorResponses) {
		super();
		assert summarySource != null;
		mSummarySource = summarySource;
		assert spoilerDestinationState != null;
		mSpoilerDestinationState = spoilerDestinationState;
		assert !duplicatorResponses.isEmpty();
		mDuplicatorResponses = duplicatorResponses;
	}

	/**
	 * @return the summarySource.
	 */
	public IGameState getSummarySource() {
		return mSummarySource;
	}

	/**
	 * @return the spoilerDestinationState.
	 */
	public STATE getSpoilerDestinationState() {
		return mSpoilerDestinationState;
	}

	/**
	 * @return the duplicatorResponses.
	 */
	public Map<IGameState, Integer> getDuplicatorResponses() {
		return mDuplicatorResponses;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDuplicatorResponses == null) ? 0 : mDuplicatorResponses.hashCode());
		result = prime * result + ((mSpoilerDestinationState == null) ? 0 : mSpoilerDestinationState.hashCode());
		result = prime * result + ((mSummarySource == null) ? 0 : mSummarySource.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final GameCallReturnSummary<?> other = (GameCallReturnSummary<?>) obj;
		if (mDuplicatorResponses == null) {
			if (other.mDuplicatorResponses != null) {
				return false;
			}
		} else if (!mDuplicatorResponses.equals(other.mDuplicatorResponses)) {
			return false;
		}
		if (mSpoilerDestinationState == null) {
			if (other.mSpoilerDestinationState != null) {
				return false;
			}
		} else if (!mSpoilerDestinationState.equals(other.mSpoilerDestinationState)) {
			return false;
		}
		if (mSummarySource == null) {
			if (other.mSummarySource != null) {
				return false;
			}
		} else if (!mSummarySource.equals(other.mSummarySource)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "Source:" + mSummarySource + ", SpoilerDestinationState:" + mSpoilerDestinationState
				+ ", DuplicatorResponses:" + mDuplicatorResponses + "]";
	}

}
