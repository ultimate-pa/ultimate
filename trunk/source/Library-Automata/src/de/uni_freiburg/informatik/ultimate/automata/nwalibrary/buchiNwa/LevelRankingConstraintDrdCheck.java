/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation3;

/**
 * LevelRankingConstraintWithDelayedRankDecreaseCheck
 * @author Matthias Heizmann
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class LevelRankingConstraintDrdCheck<LETTER, STATE> extends LevelRankingConstraint<LETTER, STATE> {
	
	
	private final HashRelation3<StateWithRankInfo<STATE>, STATE, Integer> m_RankConstraintsOfNonFinalPredecessors;

	public LevelRankingConstraintDrdCheck(INestedWordAutomatonSimple<LETTER, STATE> operand,
			int userDefinedMaxRank, boolean useDoubleDeckers) {
		super(operand, userDefinedMaxRank, useDoubleDeckers);
		m_RankConstraintsOfNonFinalPredecessors = new HashRelation3<>();
	}
	
	/**
	 * {@inheritDoc}
	 */
	public LevelRankingConstraintDrdCheck() {
		super();
		m_RankConstraintsOfNonFinalPredecessors = null;
	}

	@Override
	protected void addConstaint(StateWithRankInfo<STATE> down, STATE up, Integer rank, boolean oCandidate,
			boolean predecessorWasAccepting) {
		if (!predecessorWasAccepting) {
			m_RankConstraintsOfNonFinalPredecessors.addTriple(down, up, rank);
		}
		super.addConstaint(down, up, rank, oCandidate, predecessorWasAccepting);
	}
	
	public boolean aroseFromDelayedRankDecrease() {
		for (StateWithRankInfo<STATE> down : m_RankConstraintsOfNonFinalPredecessors.projectToFst()) {
			for (STATE up : m_RankConstraintsOfNonFinalPredecessors.projectToSnd(down)) {
				Set<Integer> ranks = m_RankConstraintsOfNonFinalPredecessors.projectToTrd(down, up);
				for (Integer rank : ranks) {
					// return true if ranks contains two successive numbers
					// x and x+1 such that x is odd.
					if (isOdd(rank)) {
						if (ranks.contains(rank + 1)) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	
	

}
