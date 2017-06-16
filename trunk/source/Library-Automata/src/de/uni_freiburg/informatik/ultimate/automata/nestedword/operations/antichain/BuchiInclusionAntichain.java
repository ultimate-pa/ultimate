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
 * make use of Antichain
 * @author liyong (liyong@ios.ac.cn)
 * **/
public class BuchiInclusionAntichain implements IBuchiInclusion {
	
	private final IBuchi mFstOperand;
	private final IBuchi mSndOperand;
	private final BuchiComplementSDBA mSndComplement;
	
	private final IBuchi mResult;
	// use antichain to accelerate inclusion check
	private final Antichain mAntichain;
	
	public BuchiInclusionAntichain(IBuchi fstOp, IBuchi sndOp) {
		this.mFstOperand = fstOp;
		this.mSndOperand = sndOp;
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
	@Override
	public Boolean isIncluded(final AutomataLibraryServices services) {
		Tarjan scc = new Tarjan(services);
//		System.out.println(mAntichain.toString() );
//		System.out.println(mResult.toString());
//		System.out.println(mFstFinalStates + ", " + mSndFinalStates);
		return scc.isEmpty();
	}
	

	@Override
	public IBuchi getFstBuchi() {
		return mFstOperand;
	}
	
	@Override
	public IBuchi getSndBuchi() {
		return mSndOperand;
	}

	@Override
	public IBuchi getSndBuchiComplement() {
		return mSndComplement;
	}
	
	@Override
	public IBuchi getBuchiDifference() {
		return mResult;
	}

	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		return null;
	}

	@Override
	public IPair<List<IState>, List<IState>> getCounterexampleRun() {
		return null;
	}
	
	// ---------------------------- part for SCC decomposition -------------
	
	/**
	 * SCC Decomposition
	 * */
	private class Tarjan {
		
		private int mIndex=0;
		private final Stack<Integer> mStack = new Stack<Integer>();
		private final Map<Integer,Integer> mIndexMap = new HashMap<Integer,Integer>();
		private final Map<Integer,Integer> mLowlinkMap = new HashMap<Integer,Integer>();
		
		private final AutomataLibraryServices mServices;
		private Boolean mEmpty ;
		
		public Tarjan(final AutomataLibraryServices services) {
			this.mServices = services;
			for(int n = mResult.getInitialStates().nextSetBit(0);
					n >= 0;
					n = mResult.getInitialStates().nextSetBit(n + 1)) {
				if(! mIndexMap.containsKey(n) && ! terminate()){
					tarjan(n);
				}
			}
		}
		
		private boolean terminate() {
			if(mServices == null) {
				return false;
			}
			return ! mServices.getProgressAwareTimer().continueProcessing();
		}
		
		public Boolean isEmpty() {
			return mEmpty;
		}
		
		// make use of tarjan algorithm
		void tarjan(int v) {
			if(terminate()) {
				mEmpty = null;
				return ;
			}
			mIndexMap.put(v, mIndex);
			mLowlinkMap.put(v, mIndex);
			mIndex++;
			mStack.push(v);
			InclusionPairNCSB pair = mPairNCSBArray.get(v);
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
						if(! mIndexMap.containsKey(stateSucc.getId()) && mAntichain.addPair(fstSucc, yState)){
							tarjan(stateSucc.getId());
							if(! mEmpty || terminate()) return ;
							mLowlinkMap.put(v,	Math.min(mLowlinkMap.get(v), mLowlinkMap.get(stateSucc.getId())));
						}else if(mStack.contains(stateSucc.getId())){
							mLowlinkMap.put(v,	Math.min(mLowlinkMap.get(v), mIndexMap.get(stateSucc.getId())));
						}
					}
				}
			}
			
			if(mLowlinkMap.get(v).intValue() == mIndexMap.get(v).intValue()){
				boolean hasFstAcc = false, hasSndAcc = false;
				// In order to get the accepting run, we have to use list in the future
				BitSet scc = new BitSet();
				while(! mStack.empty()){
					Integer t = mStack.pop();
					scc.set(t);
					InclusionPairNCSB sp = mPairNCSBArray.get(t);
					if(mFstOperand.isFinal(sp.getFstElement())) hasFstAcc = true;
					if(mSndComplement.isFinal(sp.getSndElement())) hasSndAcc = true;
					if(t.intValue() == v)
						break;
				}
				
				mEmpty = ! (hasFstAcc && hasSndAcc);
				if(scc.cardinality() == 1 // only has a single state
						&& ! mEmpty        // it is an accepting states
						) {
					IState s = mResult.getState(v);
					boolean hasSelfLoop = false;
					for(Integer letter : s.getEnabledLetters()) {
						if(s.getSuccessors(letter).get(v)) hasSelfLoop = true;
					}
					if(!hasSelfLoop) mEmpty = true;
				}
				if(! mEmpty) return ;
			}
		}
		
	}
	
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
		
		BuchiInclusionAntichain inclusionChecker = new BuchiInclusionAntichain(A, B);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
		
		inclusionChecker = new BuchiInclusionAntichain(A, C);
//		System.out.println(inclusionChecker.isIncluded2());
		System.out.println(inclusionChecker.isIncluded(null));
	}

}
