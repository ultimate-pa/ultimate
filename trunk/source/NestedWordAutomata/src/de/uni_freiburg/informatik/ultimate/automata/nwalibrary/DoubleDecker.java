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

/**
 * Part of a NestedWordAutomatons configuration. up is the state in which
 * the automaton is. down is the state before the last call transition
 * that the automaton has taken.
 * <p>
 * For many algorithms (e.g. determinization) we do not have to use 
 * configurations (current state + stack) of the automaton, the DoubleDeckers
 * are sufficient. In 
 * "JACM2009 - Alur,Madhusudan - Adding nesting structure to words"
 * a DoubleDeckers is called "summary state", but to avoid clashes in variable
 * names I decided to use this name.
 *  
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class DoubleDecker<C> {
	private final C m_Down;
	private final C m_Up;
	private final int hashCode;
	
	public DoubleDecker(C down, C up) {
		this.m_Down = down;
		this.m_Up = up;
		
		this.hashCode = 
			3 * this.m_Down.hashCode() + 5 * this.m_Up.hashCode();
	}
	
	public C getDown() {
		return m_Down;
	}


	public C getUp() {
		return m_Up;
	}
	

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof DoubleDecker) {
			DoubleDecker<C> summaryState = (DoubleDecker<C>) obj;
			return m_Up.equals(summaryState.m_Up) && 
							m_Down.equals(summaryState.m_Down);
		}
		else {
			return false;
		}
	}
	
	@Override
	public int hashCode() {
		return hashCode;
	}

	@Override
	public String toString() {
		return "Basement: " + m_Down + "  Upstairs: " + m_Up;
	}
	
}
