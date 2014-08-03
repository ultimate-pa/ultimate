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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class Transition<S, C> implements ITransition<S, C>, Serializable,
		Comparable<Transition<S, C>> {
	private static final long serialVersionUID = 5948089529814334197L;

	private final int m_HashCode;
	private final S m_Symbol;
	private final Collection<Place<S, C>> m_Predecessors;
	private final Collection<Place<S, C>> m_Successors;

	private final int m_TotalOrderID;

	public Transition(S symbol, Collection<Place<S, C>> predecessors,
			Collection<Place<S, C>> successors, int totalOrderID) {
		m_Symbol = symbol;
		m_Predecessors = Collections
				.unmodifiableList((List<Place<S, C>>) predecessors);
		m_Successors = Collections
				.unmodifiableList((List<Place<S, C>>) successors);
		m_HashCode = computeHashCode();
		m_TotalOrderID = totalOrderID;
	}

	@Override
	public S getSymbol() {
		return m_Symbol;
	}

	@Override
	public Collection<Place<S, C>> getPredecessors() {
		return m_Predecessors;
	}

	@Override
	public Collection<Place<S, C>> getSuccessors() {
		return m_Successors;
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}

	public int computeHashCode() {
		return 13 * m_Predecessors.hashCode() + 7 * m_Successors.hashCode() + 3
				* m_Symbol.hashCode();
	}

	@Override
	public String toString() {
		return m_Symbol.toString()+"["+m_TotalOrderID+"]";
	}

	public int getTotalOrderID() {
		return m_TotalOrderID;
	}

	@Override
	public int compareTo(Transition<S, C> o) {
		return m_TotalOrderID - o.m_TotalOrderID;
	}

}
