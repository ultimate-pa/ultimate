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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;



/**
 * only valid for automata pair whose second element is an SDBA
 * @author liyong (liyong@ios.ac.cn)
 * **/
public class BuchiInclusionNestedDFS implements IBuchiInclusion {
	
	private final IBuchi mFstOperand;
	private final BuchiComplementSDBA mSndComplement;
	
	private final IBuchi mResult;
	// use antichain to accelerate inclusion check
	private final Antichain mAntichain;
	
	public BuchiInclusionNestedDFS(IBuchi fstOp, IBuchi sndOp) {
		this.mFstOperand = fstOp;
		this.mSndComplement = new BuchiComplementSDBA(sndOp);
		this.mResult = new BuchiGeneral(fstOp.getAlphabetSize());
		this.mAntichain = new Antichain();
		computeInitalStates();
	}
	
	private void computeInitalStates() {
		// TODO Auto-generated method stub
		for(int fst = mFstOperand.getInitialStates().nextSetBit(0);
				fst >= 0;
				fst = mFstOperand.getInitialStates().nextSetBit(fst + 1)) {
			for(int snd = mSndComplement.getInitialStates().nextSetBit(0);
					snd >= 0;
					snd = mSndComplement.getInitialStates().nextSetBit(snd + 1)) {
				StateNCSB sndState = (StateNCSB)mSndComplement.getState(snd);
				if(mAntichain.addPair(fst, sndState)) {
					InclusionPairNCSB pair = new InclusionPairNCSB(fst, sndState);
					IState state = getOrAddState(pair);
					mResult.setInitial(state);
				}
			}
		}
	}

	private final Map<InclusionPairNCSB, IState> mPairStateMap = new HashMap<>();
	private final BitSet mFstFinalStates = new BitSet();
	private final BitSet mSndFinalStates = new BitSet();
	private final List<InclusionPairNCSB> mPairNCSBArray = new ArrayList<>();
	
	private IState getOrAddState(InclusionPairNCSB pair) {
		IState state = mPairStateMap.get(pair);
		if(state == null) {
			state = mResult.addState();
			mPairNCSBArray.add(pair);
			mPairStateMap.put(pair, state);
			if(mFstOperand.isFinal(pair.getFstElement())) mFstFinalStates.set(state.getId());
			if(mSndComplement.isFinal(pair.getSndElement())) mSndFinalStates.set(state.getId());
		}
		return state;
	}
		
	/**
	 * try to compute the product of mFstOperand and mSndComplement
	 * and avoid exploring unnecessary states as much as possible
	 * */
	
	public Boolean isIncluded(final AutomataLibraryServices services) {

		return null;
	}
	
	// ---------------------------- part for SCC decomposition -------------
	
	private class NestedDFS {
		private final Stack<Integer> mFstStack;
		private final Stack<Integer> mSndStack;
		private final BitSet mFstTable;
		private final BitSet mSndTable;
		private Boolean mIsEmpty;
		
		NestedDFS() {
			mFstStack = new Stack<>();
			mSndStack = new Stack<>();
			mFstTable = new BitSet();
			mSndTable = new BitSet();
			
			explore();
		}

		private void explore() {
			// TODO Auto-generated method stub
			for(int n = mResult.getInitialStates().nextSetBit(0);
					n >= 0;
					n = mResult.getInitialStates().nextSetBit(n + 1)) {
				if(!mFstTable.get(n)){
					fstDFS(n);
				}
			}
		}

		private void fstDFS(int n) {
			// TODO Auto-generated method stub
			mFstStack.push(n);
			mFstTable.set(n);
			// explore
		}
		
		private void sndDFS(int n) {
			
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
		
		BuchiInclusionNestedDFS inclusionChecker = new BuchiInclusionNestedDFS(A, B);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
		
		inclusionChecker = new BuchiInclusionNestedDFS(A, C);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
	}

	@Override
	public IBuchi getFstBuchi() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IBuchi getSndBuchi() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IBuchi getSndBuchiComplement() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IBuchi getBuchiDifference() {
		// TODO Auto-generated method stub
		return null;
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

}
