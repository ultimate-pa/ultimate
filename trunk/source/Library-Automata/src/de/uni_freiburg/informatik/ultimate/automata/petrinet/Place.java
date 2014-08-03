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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;

public class Place<S,C> implements Serializable {
	private static final long serialVersionUID = -4577818193149596161L;

	private final int m_HashCode;
	
	static int s_SerialNumberCounter = 0;
	
	private final C m_Content;
	private final ArrayList<ITransition<S,C>> m_Predecessors;
	private final ArrayList<ITransition<S,C>> m_Successors;
	
	private final int m_SerialNumber = s_SerialNumberCounter++;
	
	
	
	public Place(C content) {
		this.m_Content = content;
		this.m_Predecessors = new ArrayList<ITransition<S,C>>();
		this.m_Successors = new ArrayList<ITransition<S,C>>();
		m_HashCode = computeHashCode();
	}
	
	public C getContent() {
		return m_Content;
	}
	
	public Collection<ITransition<S, C>> getPredecessors() {
		return m_Predecessors;
	}
	
	public Collection<ITransition<S, C>> getSuccessors() {
		return m_Successors;
	}
	
	public void addPredecessor(ITransition<S,C> transition) {
		m_Predecessors.add(transition);
	}
	
	public void addSuccessor(ITransition<S,C> transition) {
		m_Successors.add(transition);
	}
	
	@Override
	public String toString() {
		return String.valueOf(m_Content);
	}
	
	public String toStringWithSerial() {
		return "#"+ m_SerialNumber + "#" + String.valueOf(m_Content);
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}
	
	public int computeHashCode() {
		return m_SerialNumber;
	}
	
}
