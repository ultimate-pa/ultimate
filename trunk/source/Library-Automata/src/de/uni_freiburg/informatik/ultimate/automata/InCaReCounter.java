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
package de.uni_freiburg.informatik.ultimate.automata;

/**
 * Three counters, one for internal, one for call, one for return.
 * @author Matthias Heizmann
 *
 */
public class InCaReCounter {
	private int m_Internal;
	private int m_Call;
	private int m_Return;
	
	public InCaReCounter() {
		super();
		m_Internal = 0;
		m_Call = 0;
		m_Return = 0;
	}
	public int getInternal() {
		return m_Internal;
	}
	public int getCall() {
		return m_Call;
	}
	public int getReturn() {
		return m_Return;
	}
	
	public void incIn() {
		m_Internal++;
	}
	
	public void incCa() {
		m_Call++;
	}
	
	public void incRe() {
		m_Return++;
	}
	
	@Override
	public String toString() {
		return m_Internal + "In " + m_Call + "Ca " + m_Return + "Re"; 
	}
	
	
	/**
	 * Add all values of another counter to the values of this counter.
	 */
	public void add(InCaReCounter inCaReCounter) {
		m_Internal += inCaReCounter.getInternal();
		m_Call += inCaReCounter.getCall();
		m_Return =+ inCaReCounter.getReturn();
	}

}
