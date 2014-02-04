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
 * Outgoing internal transition of a state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class OutgoingInternalTransition<LETTER,STATE> implements Transitionlet<LETTER,STATE> {
	
	private final LETTER m_Letter; 
	private final STATE m_Succ;
	
	public OutgoingInternalTransition(LETTER letter, STATE succ) {
		m_Letter = letter;
		m_Succ = succ;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	public STATE getSucc() {
		return m_Succ;
	}
	
	public String toString() {
		return MessageFormat.format("( _ , {0} , {1} )", getLetter(), getSucc());
	}
	
}
