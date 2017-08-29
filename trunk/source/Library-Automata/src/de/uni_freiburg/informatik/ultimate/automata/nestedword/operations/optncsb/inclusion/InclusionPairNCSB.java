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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateGeneral;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.StateNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IPair;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public class InclusionPairNCSB implements IPair<Integer, StateNCSB>{
	
	private final int mFstStateId;
	private final StateNCSB mSndState;
		
	public InclusionPairNCSB(StateGeneral fstState, StateNCSB sndState) {
		this.mFstStateId = fstState.getId();
		this.mSndState = sndState;
	}
	
	public InclusionPairNCSB(int fstStateId, StateNCSB sndState) {
		this.mFstStateId = fstStateId;
		this.mSndState = sndState;
	}
	
	@Override
	public boolean equals(Object other) {
		if(! (other instanceof InclusionPairNCSB)) {
			return false;
		}
		// check equivalence
		InclusionPairNCSB otherState = (InclusionPairNCSB)other;
		return mFstStateId == otherState.mFstStateId
		  &&  mSndState.equals(otherState.mSndState);
	}
	
	@Override
	public String toString() {
		return "(" + mFstStateId + "," + mSndState.toString() + ")";
	}
	
	int hashCode;
	boolean hasCode = false;
	@Override
	public int hashCode() {
		if(hasCode) return hashCode;
		else {
			hasCode = true;
			hashCode = toString().hashCode();
		}
		return hashCode;
	}
	
	// by definition, if true, the language of this pair is covered 
	public boolean coveredBy(InclusionPairNCSB other) {
		return mFstStateId == other.mFstStateId
		  &&  mSndState.coveredBy(other.mSndState);
	}
	
	public boolean strictlyCoveredBy(InclusionPairNCSB other) {
		return mFstStateId == other.mFstStateId
				  &&  mSndState.strictlyCoveredBy(other.mSndState);
	}
	
	@Override
	public Integer getFstElement() {
		return mFstStateId;
	}
	
	@Override
	public StateNCSB getSndElement() {
		return mSndState;
	}
}