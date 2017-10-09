/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

public class GeneralizedState extends StateWa {

	private final GeneralizedBuchiIntersection mBuchi;
	
	public GeneralizedState(GeneralizedBuchiIntersection buchi, int id) {
		super(id);
		this.mBuchi = buchi;
	}
	
	private int mLeft;
	private int mRight;
	
	protected void setPairs(int left, int right) {
		mLeft = left;
		mRight = right;
	}
	
	public boolean equals(Object obj) {
		if(this == obj) return true;
		if(!(obj instanceof GeneralizedState)) {
			return false;
		}
		GeneralizedState other = (GeneralizedState)obj;
		return mLeft == other.mLeft && mRight == other.mRight;
	}
	
	public String toString() {
		return "(" + mLeft + "," + mRight + ")";
	}
	
	@Override
	public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + mLeft;
        result = prime * result + mRight;
        return result;
	}
	
	public int getLeft() {
		return mLeft;
	}
	
	public int getRight() {
		return mRight;
	}
	
	private IntSet visitedLetters = UtilIntSet.newIntSet();
	
	@Override
	public IntSet getSuccessors(int letter) {
		if(visitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		
		visitedLetters.set(letter);
		// compute successors
		IBuchiWa fstOp = mBuchi.getFirstOperand();
		IBuchiWa sndOp = mBuchi.getSecondOperand();
		IntSet fstSuccs = fstOp.getState(mLeft).getSuccessors(letter);
		IntSet sndSuccs = sndOp.getState(mRight).getSuccessors(letter);
		
		IntSet succs = UtilIntSet.newIntSet();
		for(final Integer fstSucc : fstSuccs.iterable()) {
			for(final Integer sndSucc : sndSuccs.iterable()) {
				// pair (X, Y)
				GeneralizedState succ = mBuchi.addState(fstSucc, sndSucc);                
				this.addSuccessor(letter, succ.getId());
				succs.set(succ.getId());
			}
		}

		return succs;
	}

}
