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


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiGeneral;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IState;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

/**
 * only valid for semi-deterministic Buchi automaton
 * */

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public class BuchiComplementSDBA extends BuchiGeneral implements IBuchiComplement {

	private final IBuchi mOperand;
	
//	private final List<IntSet> mOpTransUsed;
	
	public BuchiComplementSDBA(IBuchi buchi) {
		super(buchi.getAlphabetSize());
		// TODO Auto-generated constructor stub
		this.mOperand = buchi;
//		this.mOpTransUsed = new ArrayList<>();
//		for(int i = 0; i < mOperand.getAlphabetSize(); i ++) {
//			this.mOpTransUsed.add(UtilIntSet.newIntSet());
//		}
		computeInitialStates();
	}
	
	private final TObjectIntMap<StateNCSB> mState2Int = new TObjectIntHashMap<>();

	private void computeInitialStates() {
		StateNCSB state = new StateNCSB(0, this);
		IntSet C = mOperand.getInitialStates().clone();
		C.and(mOperand.getFinalStates()); // goto C
		IntSet N = mOperand.getInitialStates().clone();
		N.andNot(mOperand.getFinalStates());
		state.setSets(N, C, UtilIntSet.newIntSet(), C);
		if(C.isEmpty()) this.setFinal(0);
		this.setInitial(0);
		int id = this.addState(state);
		mState2Int.put(state, id);
	}
	
	public StateNCSB getNCSBState(int id) {
		return (StateNCSB) getState(id);
	}

	protected StateNCSB addState(IntSet N, IntSet C, IntSet S, IntSet B) {
		
		StateNCSB state = new StateNCSB(0, this);
		state.setSets(N, C, S, B);
		
		if(mState2Int.containsKey(state)) {
			return (StateNCSB) getState(mState2Int.get(state));
		}else {
			int index = getStateSize();
			StateNCSB newState = new StateNCSB(index, this);
			newState.setSets(N, C, S, B);
			int id = this.addState(newState);
			mState2Int.put(newState, id);
			
			if(B.isEmpty()) setFinal(index);
			
			return newState;
		}
	}

	@Override
	public IBuchi getOperand() {
		return mOperand;
	}
	
	
	private boolean mExplored = false;
	
	public void explore() {
		
		if(mExplored) return ;
		
		mExplored = true;
		
		LinkedList<IState> walkList = new LinkedList<>();
		IntSet initialStates = getInitialStates();
		
		IntIterator iter = initialStates.iterator();
		while(iter.hasNext()) {
			walkList.addFirst(getState(iter.next()));
		}

		
        BitSet visited = new BitSet();
        
        while(! walkList.isEmpty()) {
        	IState s = walkList.remove();
        	if(visited.get(s.getId())) continue;
        	visited.set(s.getId());
        	if(Options.verbose) System.out.println("s"+ s.getId() + ": " + s.toString());
        	for(int i = 0; i < mOperand.getAlphabetSize(); i ++) {
        		IntSet succs = s.getSuccessors(i);
        		iter = succs.iterator();
        		while(iter.hasNext()) {
        			int n = iter.next();
        			if(Options.verbose) System.out.println(" s"+ s.getId() + ": " + s.toString() + "- L" + i + " -> s" + n + ": " + getState(n));
        			if(! visited.get(n)) {
        				walkList.addFirst(getState(n));
        			}
        		}
        	}
        }
	}


//	@Override
//	public void useOpTransition(int letter, IntSet states) {
//		// TODO Auto-generated method stub
////		this.mOpTransUsed.get(letter).or(states);
//	}
//
//
//	@Override
//	public int getNumUsedOpTransition() {
//		// TODO Auto-generated method stub
//		int num = 0;
////		for(int i = 0; i < mOpTransUsed.size(); i ++) {
////			IntSet sources = mOpTransUsed.get(i);
////			IntIterator iter = sources.iterator();
////			while(iter.hasNext()) {
////				num += mOperand.getState(iter.next()).getSuccessors(i).cardinality();
////			}
////		}
//		return num;
//	}
	
	
}
