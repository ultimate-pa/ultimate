/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions;

import java.text.MessageFormat;

/**
 * Outgoing call transition of a state.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class OutgoingCallTransition<LETTER, STATE> implements IOutgoingTransitionlet<LETTER, STATE> {
	private final LETTER mLetter;
	private final STATE mSucc;
	
	/**
	 * Constructor.
	 * 
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 */
	public OutgoingCallTransition(final LETTER letter, final STATE succ) {
		mLetter = letter;
		mSucc = succ;
	}
	
	@Override
	public LETTER getLetter() {
		return mLetter;
	}
	
	@Override
	public STATE getSucc() {
		return mSucc;
	}
	
	@Override
	public String toString() {
		return MessageFormat.format("( _ , {0} , {1} )", getLetter(), getSucc());
	}
}
