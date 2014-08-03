/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;

class Summary<LETTER, STATE> {
	private final StateContainer<LETTER, STATE> m_HierPred;
	private final StateContainer<LETTER, STATE> m_LinPred;
	private final LETTER m_Letter;
	private final StateContainer<LETTER, STATE> m_Succ;
	public Summary(StateContainer<LETTER, STATE> hierPred, 
			StateContainer<LETTER, STATE> linPred,
			LETTER letter,
			StateContainer<LETTER, STATE> succ) {
		super();
		m_HierPred = hierPred;
		m_LinPred = linPred;
		m_Letter = letter;
		m_Succ = succ;
	}
	public StateContainer<LETTER, STATE> getHierPred() {
		return m_HierPred;
	}
	public StateContainer<LETTER, STATE> getLinPred() {
		return m_LinPred;
	}
	public LETTER getLetter() {
		return m_Letter;
	}
	public StateContainer<LETTER, STATE> getSucc() {
		return m_Succ;
	}
	

	
	public IncomingReturnTransition<LETTER, STATE> obtainIncomingReturnTransition(
			NestedWordAutomatonReachableStates<LETTER, STATE> nwars) {
		for (IncomingReturnTransition<LETTER, STATE> inTrans  : 
			nwars.returnPredecessors(getHierPred().getState(), getLetter(), getSucc().getState())) {
			if (getLinPred().getState().equals(inTrans.getLinPred())) {
				return inTrans;
			}
		}
		throw new AssertionError("no such transition");
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_HierPred == null) ? 0 : m_HierPred.hashCode());
		result = prime * result
				+ ((m_LinPred == null) ? 0 : m_LinPred.hashCode());
		result = prime * result
				+ ((m_Succ == null) ? 0 : m_Succ.hashCode());
		return result;
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Summary other = (Summary) obj;
		if (m_HierPred == null) {
			if (other.m_HierPred != null)
				return false;
		} else if (!m_HierPred.equals(other.m_HierPred))
			return false;
		if (m_LinPred == null) {
			if (other.m_LinPred != null)
				return false;
		} else if (!m_LinPred.equals(other.m_LinPred))
			return false;
		if (m_Succ == null) {
			if (other.m_Succ != null)
				return false;
		} else if (!m_Succ.equals(other.m_Succ))
			return false;
		return true;
	}
	@Override
	public String toString() {
		return "(" + m_HierPred + ", " + m_LinPred + ", " + m_Succ + ")";
	}
	
	
}
