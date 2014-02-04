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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.text.MessageFormat;


/**
 * Return Transition of a successor state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IncomingReturnTransition<LETTER,STATE> implements Transitionlet<LETTER,STATE> {
	
	private final STATE m_LinPred;
	private final STATE m_HierPred;
	private final LETTER m_Letter; 

	
	public IncomingReturnTransition(STATE linPred, STATE hierPred, LETTER letter) {
		m_LinPred = linPred;
		m_HierPred = hierPred;
		m_Letter = letter;
	}
	
	public STATE getLinPred() {
		return m_LinPred;
	}
	
	public STATE getHierPred() {
		return m_HierPred;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	
	public String toString() {
		return MessageFormat.format("( {0} , {1} , {2} , _ )",getLinPred(), getHierPred(), getLetter());
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_HierPred == null) ? 0 : m_HierPred.hashCode());
		result = prime * result
				+ ((m_Letter == null) ? 0 : m_Letter.hashCode());
		result = prime * result
				+ ((m_LinPred == null) ? 0 : m_LinPred.hashCode());
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
		IncomingReturnTransition other = (IncomingReturnTransition) obj;
		if (m_HierPred == null) {
			if (other.m_HierPred != null)
				return false;
		} else if (!m_HierPred.equals(other.m_HierPred))
			return false;
		if (m_Letter == null) {
			if (other.m_Letter != null)
				return false;
		} else if (!m_Letter.equals(other.m_Letter))
			return false;
		if (m_LinPred == null) {
			if (other.m_LinPred != null)
				return false;
		} else if (!m_LinPred.equals(other.m_LinPred))
			return false;
		return true;
	}
	
	
	
}
