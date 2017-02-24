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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Node in the graph that we build for computation of summaries.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class SummaryComputationGraphNode<LETTER, STATE> {

	private final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> mSource2Current2Targets;
	private final Set<IGameState> mSummaryComputationTriggers;

	public SummaryComputationGraphNode(
			final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> source2Current2Targets,
			final Set<IGameState> summaryComputationTriggers) {
		super();
		mSource2Current2Targets = source2Current2Targets;
		mSummaryComputationTriggers = summaryComputationTriggers;
	}

	public Set<IGameState> getSources() {
		return mSource2Current2Targets.keySet();
	}

	public Set<IGameState> getCurrent(final IGameState source) {
		return mSource2Current2Targets.get(source).keySet();
	}

	public Map<IGameState, WeightedSummaryTargets> getCurrent2Targets(final IGameState source) {
		return mSource2Current2Targets.get(source);
	}

//
//	public final WeightedSummaryTargets getWeightedSummaryTargets(final IGameState current) {
//		return mCurrent2Targets.get(current);
//	}

	public NestedMap2<IGameState, IGameState, WeightedSummaryTargets> getSource2Current2Targets() {
		return mSource2Current2Targets;
	}

//	/**
//	 * @return the current2Targets
//	 */
//	public Map<IGameState, WeightedSummaryTargets> getCurrent2Targets() {
//		return mCurrent2Targets;
//	}

	/**
	 * @return the summaryComputationTriggers.
	 */
	public Set<IGameState> getSummaryComputationTriggers() {
		return mSummaryComputationTriggers;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mSource2Current2Targets == null) ? 0 : mSource2Current2Targets.hashCode());
		result = prime * result + ((mSummaryComputationTriggers == null) ? 0 : mSummaryComputationTriggers.hashCode());
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
		final SummaryComputationGraphNode<?, ?> other = (SummaryComputationGraphNode<?, ?>) obj;
		if (mSource2Current2Targets == null) {
			if (other.mSource2Current2Targets != null) {
				return false;
			}
		} else if (!mSource2Current2Targets.equals(other.mSource2Current2Targets)) {
			return false;
		}
		if (mSummaryComputationTriggers == null) {
			if (other.mSummaryComputationTriggers != null) {
				return false;
			}
		} else if (!mSummaryComputationTriggers.equals(other.mSummaryComputationTriggers)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return mSource2Current2Targets.keySet().size() + " sources " + mSource2Current2Targets.size()
				+ " source-current pairs";
	}
}
