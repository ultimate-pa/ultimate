/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Represents a state of the subset component.
 * 
 * @author Matthias Heizmann
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class FkvSubsetComponentState<LETTER, STATE> implements IFkvState<LETTER, STATE> {
	
	private final DeterminizedState<LETTER, STATE> mDeterminizedState;
	private final HashRelation<StateWithRankInfo<STATE>, StateWithRankInfo<STATE>> mDown2Up;
	

	FkvSubsetComponentState(final DeterminizedState<LETTER, STATE> detState) {
		mDeterminizedState = detState;
		mDown2Up = new HashRelation<>();
		for (final STATE down : detState.getDownStates()) {
			for (final STATE up : detState.getUpStates(down)) {
				mDown2Up.addPair(new StateWithRankInfo<STATE>(down), new StateWithRankInfo<STATE>(up));
			}
		}
	}
	
	public DeterminizedState<LETTER, STATE> getDeterminizedState() {
		return mDeterminizedState;
	}

	@Override
	public Set<StateWithRankInfo<STATE>> getDownStates() {
		return mDown2Up.getDomain();
	}

	@Override
	public Iterable<StateWithRankInfo<STATE>> getUpStates(
			final StateWithRankInfo<STATE> downState) {
		return mDown2Up.getImage(downState);
	}

	@Override
	public String toString() {
		return mDeterminizedState.toString();
	}
	
	@Override
	public int hashCode() {
		return mDeterminizedState.hashCode();
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
		final FkvSubsetComponentState other = (FkvSubsetComponentState) obj;
		if (mDeterminizedState == null) {
			if (other.mDeterminizedState != null) {
				return false;
			}
		} else if (!mDeterminizedState.equals(other.mDeterminizedState)) {
			return false;
		}
		return true;
	}
	

	
	


}
