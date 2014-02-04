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
 * Internal Transition of a successor state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IncomingInternalTransition<LETTER,STATE> implements Transitionlet<LETTER,STATE> {
	
	private final LETTER m_Letter; 
	private final STATE m_Pred;
	
	public IncomingInternalTransition(STATE pred, LETTER letter) {
		m_Pred = pred;
		m_Letter = letter;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	public STATE getPred() {
		return m_Pred;
	}
	
	
	public String toString() {
		return MessageFormat.format("( {0} , {1} , _ )",getPred(), getLetter());
	}
}
