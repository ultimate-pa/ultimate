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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IStateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntStack;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TIntIntMap;
import gnu.trove.map.hash.TIntIntHashMap;



public class AsccWaExploration implements EmptinessExploration{
    
	private final IBuchiWa mBuchi;
	private Ascc mAscc;
	
	public AsccWaExploration(IBuchiWa buchi) {
		mBuchi = buchi;
	}
	
	@Override
	public Boolean isEmpty() {
	    if(mAscc == null) {
	        mAscc = new Ascc();
	    }
		return mAscc.mIsEmpty;
	}

    private class Ascc {
        
        private int mDepth;
        private final IntStack mRootsStack;             // C99 's root stack
        private final IntStack mActiveStack;            // tarjan's stack
        private final TIntIntMap mDfsNum;
        private final IntSet mCurrent;
        
        private Boolean mIsEmpty = null;
                
        public Ascc() {
            
            this.mRootsStack = new IntStack();
            this.mActiveStack = new IntStack();
            this.mDfsNum = new TIntIntHashMap();
            this.mCurrent = UtilIntSet.newIntSet();
            
            for(int n : mBuchi.getInitialStates().iterable()) {
                if(! mDfsNum.containsKey(n)){
                    strongConnect(n);
                }
            }
            
            if(mIsEmpty == null) {
                mIsEmpty = true;
            }
        }
        
        void strongConnect(int n) {
            
            ++ mDepth;
            mDfsNum.put(n, mDepth);
            mRootsStack.push(n);
            mActiveStack.push(n);
            mCurrent.set(n);
            
            IStateWa state = mBuchi.getState(n);
            for(int letter = 0; letter < mBuchi.getAlphabetSize(); letter ++) {
                for(int succ : state.getSuccessors(letter).iterable()) {
                    if(! mDfsNum.containsKey(succ)) {
                        strongConnect(succ);
                    }else if(mCurrent.get(succ)) {
                        // we have already seen it before, there is a loop
                        IntSet scc = UtilIntSet.newIntSet();
                        while(true) {
                            //pop element u
                            int u = mRootsStack.pop();
                            scc.set(u);
                            // found one accepting scc
                            if(mBuchi.getAcceptance().isAccepted(scc)) {
                                mIsEmpty = false;
                                if(Options.verbose) System.out.println("ACC: " + scc);
                            }
                            if(mDfsNum.get(u) <= mDfsNum.get(succ)) {
                                mRootsStack.push(u); // push back
                                break;
                            }
                        }
                    }
                }
            }
            
            // if current number is done, 
            // then we should remove all 
            // active states in the same scc
            if(mRootsStack.peek() == n) {
                mRootsStack.pop();
                while(true) {
                    int u = mActiveStack.pop(); // Tarjan' Stack
                    mCurrent.clear(u);
                    if(u == n) break;
                }
            }
        }
        
    }

}
