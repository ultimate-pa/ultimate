/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions;

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
	
	private final STATE mLinPred;
	private final STATE mHierPred;
	private final LETTER mLetter; 

	
	public IncomingReturnTransition(STATE linPred, STATE hierPred, LETTER letter) {
		mLinPred = linPred;
		mHierPred = hierPred;
		mLetter = letter;
	}
	
	public STATE getLinPred() {
		return mLinPred;
	}
	
	public STATE getHierPred() {
		return mHierPred;
	}
	
	public LETTER getLetter() {
		return mLetter;
	}
	
	
	public String toString() {
		return MessageFormat.format("( {0} , {1} , {2} , _ )",getLinPred(), getHierPred(), getLetter());
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mHierPred == null) ? 0 : mHierPred.hashCode());
		result = prime * result
				+ ((mLetter == null) ? 0 : mLetter.hashCode());
		result = prime * result
				+ ((mLinPred == null) ? 0 : mLinPred.hashCode());
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
		if (mHierPred == null) {
			if (other.mHierPred != null)
				return false;
		} else if (!mHierPred.equals(other.mHierPred))
			return false;
		if (mLetter == null) {
			if (other.mLetter != null)
				return false;
		} else if (!mLetter.equals(other.mLetter))
			return false;
		if (mLinPred == null) {
			if (other.mLinPred != null)
				return false;
		} else if (!mLinPred.equals(other.mLinPred))
			return false;
		return true;
	}
	
	
	
}
