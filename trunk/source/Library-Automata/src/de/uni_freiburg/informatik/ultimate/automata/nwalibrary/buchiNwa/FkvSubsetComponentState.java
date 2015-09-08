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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * 
 * Represents a state of the subset component. 
 * @author Matthias Heizmann
 *
 */
public class FkvSubsetComponentState<LETTER, STATE> implements IFkvState<LETTER, STATE> {
	
	private final DeterminizedState<LETTER, STATE> m_DeterminizedState;
	private final HashRelation<StateWithRankInfo<STATE>, StateWithRankInfo<STATE>> m_Down2Up;
	

	FkvSubsetComponentState(DeterminizedState<LETTER, STATE> detState) {
		m_DeterminizedState = detState;
		m_Down2Up = new HashRelation<>();
		for (STATE down : detState.getDownStates()) {
			for (STATE up : detState.getUpStates(down)) {
				m_Down2Up.addPair(new StateWithRankInfo<STATE>(down), new StateWithRankInfo<STATE>(up));
			}
		}
	}
	
	public DeterminizedState<LETTER, STATE> getDeterminizedState() {
		return m_DeterminizedState;
	}

	@Override
	public Set<StateWithRankInfo<STATE>> getDownStates() {
		return m_Down2Up.getDomain();
	}

	@Override
	public Iterable<StateWithRankInfo<STATE>> getUpStates(
			StateWithRankInfo<STATE> downState) {
		return m_Down2Up.getImage(downState);
	}

	@Override
	public String toString() {
		return m_DeterminizedState.toString();
	}
	
	@Override
	public int hashCode() {
		return m_DeterminizedState.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FkvSubsetComponentState other = (FkvSubsetComponentState) obj;
		if (m_DeterminizedState == null) {
			if (other.m_DeterminizedState != null)
				return false;
		} else if (!m_DeterminizedState.equals(other.m_DeterminizedState))
			return false;
		return true;
	}
	

	
	


}
