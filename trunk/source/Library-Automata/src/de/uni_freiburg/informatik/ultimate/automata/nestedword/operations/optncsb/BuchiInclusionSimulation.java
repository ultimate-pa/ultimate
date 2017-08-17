/*
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


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.antichain;

import java.util.BitSet;
import java.util.List;
import java.util.Stack;


import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;



/**
 * only valid for automata pair whose second element is an SDBA
 * @author liyong (liyong@ios.ac.cn)
 * **/
public class BuchiInclusionSimulation extends BuchiInclusion {
	

	public BuchiInclusionSimulation(IBuchi fstOp, IBuchi sndOp) {
		super(fstOp, sndOp);
	}
	
	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPair<List<IState>, List<IState>> getCounterexampleRun() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected boolean isValidPair(InclusionPairNCSB pair) {
		// TODO Auto-generated method stub
		return true;
	}

	/**
	 * try to compute the product of mFstOperand and mSndComplement
	 * and avoid exploring unnecessary states as much as possible
	 * */
	
	public Boolean isIncluded(final AutomataLibraryServices services) {
		NestedDFS finder = new NestedDFS(services);
//		System.out.println(mFstOperand.toDot());
//		System.out.println(mSndOperand.toDot());
//		System.out.println(mSndComplement.toDot());
//		System.out.println(mResult.toDot());
//		System.out.println(mFstFinalStates + "," + mSndFinalStates);
		return finder.mIsEmpty;
	}
	
	// ---------------------------- part for SCC decomposition -------------
	
	private class NestedDFS {
		private final Stack<Integer> mFstStack;
		private final Stack<Integer> mSndStack;
		private final BitSet mFstTable;
		private final BitSet mSndTable;
		private Boolean mIsEmpty = true;
		private final BitSet mOnlyInFstStack;
		private final AutomataLibraryServices mServices;
		
		NestedDFS(final AutomataLibraryServices services) {

			this.mServices = services;
			this.mFstStack = new Stack<>();
			this.mSndStack = new Stack<>();
			this.mFstTable = new BitSet();
			this.mSndTable = new BitSet();
			this.mOnlyInFstStack = new BitSet();
			explore();
		}

		private void explore() {
			// TODO Auto-generated method stub
			for(int n = mResult.getInitialStates().nextSetBit(0);
					n >= 0;
					n = mResult.getInitialStates().nextSetBit(n + 1)) {
				if(!mFstTable.get(n) && !terminate()){
					fstDFS(n);
				}
			}
		}
		
		private boolean terminate() {
			if(mServices == null)
			   return false;
			return ! mServices.getProgressAwareTimer().continueProcessing();
		}

		private void fstDFS(int n) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			// TODO Auto-generated method stub
			mFstStack.push(n);
			mFstTable.set(n);
			mOnlyInFstStack.set(n);
			// explore until we see a final state
			
			InclusionPairNCSB pair = mPairNCSBArray.get(n); //n must in mPairArray
			
			//TODO only get enabled letters
			for(int letter = 0; letter < mFstOperand.getAlphabetSize(); letter ++) {
				// X states from first BA 
				BitSet fstSuccs = mFstOperand.getSuccessors(pair.getFstElement(), letter);
				if(fstSuccs.isEmpty()) continue;
				// Y states from second BA
				BitSet sndSuccs = pair.getSndElement().getSuccessors(letter);
				for(int fstSucc = fstSuccs.nextSetBit(0); fstSucc >= 0; fstSucc = fstSuccs.nextSetBit(fstSucc + 1)) {
					for(int sndSucc = sndSuccs.nextSetBit(0); sndSucc >= 0; sndSucc = sndSuccs.nextSetBit(sndSucc + 1)) {
						// pair (X, Y)
						StateNCSB yState = (StateNCSB) mSndComplement.getState(sndSucc);
						InclusionPairNCSB pairSucc = new InclusionPairNCSB(fstSucc, yState);
						IState stateSucc = getOrAddState(pairSucc);
						mPairStateMap.get(pair).addSuccessor(letter, stateSucc.getId());
						// now current successor is stateSucc
						if(! mFstTable.get(stateSucc.getId())) fstDFS(stateSucc.getId());
					}
				}
			}
			
			// go to find a loop if n is final
			if(mSndComplement.isFinal(pair.getSndElement().getId())) {
				sndDFS(n);
				if(! mIsEmpty ) return ;
			}
			
			mFstStack.pop();
			mOnlyInFstStack.clear(n);
		}
				
		private final BitSet mFstFinalInSndStack = new BitSet();
		
		private void sndDFS(int n) {
			
			if(terminate()) {
				mIsEmpty = null;
				return ;
			}
			
			mSndStack.push(n);
			mSndTable.set(n);
			InclusionPairNCSB pair = mPairNCSBArray.get(n); //n must in mPairArray
			// fst has final in the loop
			if(mFstOperand.isFinal(pair.getFstElement())) {
				mFstFinalInSndStack.set(n);
			}
			
			for(int letter = 0; letter < mFstOperand.getAlphabetSize(); letter ++) {
				// X states from first BA 
				BitSet fstSuccs = mFstOperand.getSuccessors(pair.getFstElement(), letter);
				if(fstSuccs.isEmpty()) continue;
				// Y states from second BA
				BitSet sndSuccs = pair.getSndElement().getSuccessors(letter);
				for(int fstSucc = fstSuccs.nextSetBit(0); fstSucc >= 0; fstSucc = fstSuccs.nextSetBit(fstSucc + 1)) {
					for(int sndSucc = sndSuccs.nextSetBit(0); sndSucc >= 0; sndSucc = sndSuccs.nextSetBit(sndSucc + 1)) {
						// pair (X, Y)
						StateNCSB yState = (StateNCSB) mSndComplement.getState(sndSucc);
						InclusionPairNCSB pairSucc = new InclusionPairNCSB(fstSucc, yState);
						IState stateSucc = getOrAddState(pairSucc);
						mPairStateMap.get(pair).addSuccessor(letter, stateSucc.getId());
						// now current successor is stateSucc
						if(existLoop(stateSucc.getId()) && ! mFstFinalInSndStack.isEmpty()) {
							mIsEmpty = false;
							return ;
						}else if(! mSndTable.get(stateSucc.getId())){
							sndDFS(stateSucc.getId());
							if(! mIsEmpty ) return ;
						}
					}
				}
			}
			
			mSndStack.pop();
			mFstFinalInSndStack.clear(n);
		}
		
		// either there exists a state t in stack 1
		// or there exists a final state u such that u is not the top element and is covered by t 
		private boolean existLoop(int t) {
			
			if(mOnlyInFstStack.get(t)) {
					return true;
			}
			
			BitSet accs = (BitSet) mFstFinalStates.clone(); // get current final states
			accs.and(mOnlyInFstStack);                    // get only final states in stack1
			
			accs.clear(mFstStack.peek());                 // remove the top element
			InclusionPairNCSB tPair = mPairNCSBArray.get(t);
			for(int u = accs.nextSetBit(0); u >= 0; u = accs.nextSetBit(u + 1)) {
				InclusionPairNCSB uPair = mPairNCSBArray.get(u);
				if(uPair.coveredBy(tPair)) return true;
			}
			return false;
		}

	}
		
		
	
	
	// -----------------------------------
	
	private static BuchiGeneral getA() {
		
		BuchiGeneral buchi = new BuchiGeneral(2);
		IState aState = buchi.addState();
		IState bState = buchi.addState();
		
		aState.addSuccessor(0, aState.getId());	
		aState.addSuccessor(0, bState.getId());		

		bState.addSuccessor(0, bState.getId());
//		bState.addSuccessor(0, aState.getId());
		bState.addSuccessor(1, aState.getId());
		bState.addSuccessor(0, aState.getId());
		
		buchi.setFinal(bState);
		buchi.setInitial(aState);
		
		return buchi;
	}
	
	private static BuchiGeneral getB() {
		BuchiGeneral buchi = new BuchiGeneral(2);
		IState aState = buchi.addState();
		IState bState = buchi.addState();
		
		aState.addSuccessor(0, bState.getId());		

		bState.addSuccessor(0, bState.getId());
		bState.addSuccessor(1, aState.getId());
		
		buchi.setFinal(bState);
		buchi.setInitial(aState);
		
		return buchi;
	}
	
	private static BuchiGeneral getC() {
		BuchiGeneral buchi = new BuchiGeneral(2);
		IState aState = buchi.addState();
		IState bState = buchi.addState();
		
		aState.addSuccessor(0, bState.getId());		

		bState.addSuccessor(1, aState.getId());
		
		buchi.setFinal(bState);
		buchi.setInitial(aState);
		return buchi;
	}
	
	public static void main(String[] args) {
		
		BuchiGeneral A = getA();
		BuchiGeneral B = getB();
		BuchiGeneral C = getC();
		
		BuchiInclusionSimulation inclusionChecker = new BuchiInclusionSimulation(A, B);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
		
		inclusionChecker = new BuchiInclusionSimulation(A, C);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
	}



}
