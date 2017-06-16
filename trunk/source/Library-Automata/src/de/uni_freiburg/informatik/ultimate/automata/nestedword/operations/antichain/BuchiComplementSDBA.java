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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;


/**
 * only valid for semi-deterministic Buchi automaton
 * @author Yong Li (liyong@ios.ac.cn)
 * */
public class BuchiComplementSDBA extends BuchiGeneral implements IBuchiComplement {

	private final IBuchi mOperand;
	
	public BuchiComplementSDBA(IBuchi buchi) {
		super(buchi.getAlphabetSize());
		// TODO Auto-generated constructor stub
		this.mOperand = buchi;
		computeInitialStates();
	}
	
	private final Map<StateNCSB, Integer> mState2Int = new HashMap<>();

	private void computeInitialStates() {
		// TODO Auto-generated method stub
		StateNCSB state = new StateNCSB(0, this);
		state.setSets(mOperand.getInitialStates(), new BitSet(), new BitSet(), new BitSet());
		this.setFinal(0);
		this.setInitial(0);
		int id = this.addState(state);
		mState2Int.put(state, id);
	}
	

	public StateNCSB addState(BitSet N, BitSet C, BitSet S, BitSet B) {
		
		StateNCSB state = new StateNCSB(0, this);
		state.setSets(N, C, S, B);
		Integer index = mState2Int.get(state);
		
		if(index != null) {
			return (StateNCSB) getState(index);
		}
	
		index = getStateSize();
		StateNCSB newState = new StateNCSB(index, this);
		newState.setSets(N, C, S, B);
		int id = this.addState(newState);
		mState2Int.put(state, id);
		
		if(B.isEmpty()) setFinal(index);
		
		return newState;
	}

	@Override
	public IBuchi getOperand() {
		// TODO Auto-generated method stub
		return mOperand;
	}
	
	
	private boolean mExplored = false;
	
	public void explore() {
		
		if(mExplored) return ;
		
		mExplored = true;
		
		LinkedList<IState> walkList = new LinkedList<>();
		BitSet initialStates = getInitialStates();
		
		for(int i = initialStates.nextSetBit(0); i >= 0; i = initialStates.nextSetBit(i + 1)) {
			walkList.addFirst(getState(i));
		}
		
        BitSet visited = new BitSet();
        
        while(! walkList.isEmpty()) {
        	IState s = walkList.remove();
        	visited.set(s.getId());
        	for(int i = 0; i < mOperand.getAlphabetSize(); i ++) {
        		BitSet succs = s.getSuccessors(i);
        		for(int n = succs.nextSetBit(0); n >= 0; n = succs.nextSetBit(n + 1)) {
        			System.out.println("s"+ s.getId() + ": " + s.toString() + "- L" + i + " -> s" + n + ": " + getState(n));
        			if(! visited.get(n)) {
        				walkList.addFirst(getState(n));
        			}
        		}
        	}
        }
	}
	
	
	public static void main(String[] args) {
		
		IBuchi buchi = new BuchiGeneral(2);
		IState aState = buchi.addState();
		IState bState = buchi.addState();
		
		aState.addSuccessor(0, bState.getId());
		aState.addSuccessor(1, aState.getId());
//		aState.addSuccessor(1, aState.getId());
		
//		aState.addSuccessor(1, bState.getId());
		bState.addSuccessor(0, bState.getId());
//		bState.addSuccessor(0, aState.getId());
		bState.addSuccessor(1, aState.getId());
		
		buchi.setFinal(bState);
		buchi.setInitial(aState);
		
		System.out.println(buchi.toString());
		
		System.out.println("----------- complement buchi ---------");
		BuchiComplementSDBA complement = new BuchiComplementSDBA(buchi);
		
		complement.explore();
		System.out.println(complement.toString());

	}
	
	
}
