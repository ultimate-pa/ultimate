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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.BuchiWaComplement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.StateWaNCSB;

class DifferencePair {
    
    final int mFstState;
    final int mSndState;
    final BuchiWaComplement mSndComplement;
    
    public DifferencePair(BuchiWaComplement sndComplement, int fst, int snd) {
        mSndComplement = sndComplement;
        mFstState = fst;
        mSndState = snd;
    }
    
    @Override
    public boolean equals(Object other) {
        if(this == other) return true;
        if(! (other instanceof DifferencePair)) {
            return false;
        }
        // check equivalence
        DifferencePair otherState = (DifferencePair)other;
        return mFstState == otherState.mFstState
          &&  mSndState == otherState.mSndState;
    }
    
    @Override
    public String toString() {
        return "(" + mFstState + "," + mSndComplement.getState(mSndState).toString() + ")";
    }
    
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + mFstState;
        result = prime * result + mSndState;
        return result;
    }
    
    // by definition, if true, the language of this pair is covered 
    public boolean coveredBy(DifferencePair other) {
        if(mFstState != other.mFstState) return false;
        StateWaNCSB state = (StateWaNCSB) mSndComplement.getState(mSndState);
        StateWaNCSB otherState = (StateWaNCSB) mSndComplement.getState(other.mSndState);
        return state.getNCSB().coveredBy(otherState.getNCSB());
    }
    
    public boolean strictlyCoveredBy(DifferencePair other) {
        if(mFstState != other.mFstState) return false;
        StateWaNCSB state = (StateWaNCSB) mSndComplement.getState(mSndState);
        StateWaNCSB otherState = (StateWaNCSB) mSndComplement.getState(other.mSndState);
        return state.getNCSB().strictlyCoveredBy(otherState.getNCSB());
    }
    
    public int getFirstState() {
        return mFstState;
    }
    
    public int getSecondState() {
        return mSndState;
    }
    
}