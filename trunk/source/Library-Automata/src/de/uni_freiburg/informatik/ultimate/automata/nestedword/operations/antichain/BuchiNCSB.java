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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;



/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */
// TODO support on-demand exploration
public class BuchiNCSB<LETTER, STATE> extends BuchiGeneral {

	private final Map<LETTER, Integer> mLetterMap;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mInnerBuchi;

	private final Map<STATE, IState> mStateMap;
	private final List<STATE> mStateArr;
	private final List<LETTER> mLetterArr;
	
	public BuchiNCSB(int alphabetSize, Map<LETTER, Integer> letterMap,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> buchi) {
		super(alphabetSize);
		// TODO Auto-generated constructor stub
		this.mLetterMap = letterMap;
		this.mInnerBuchi = buchi;
		this.mStateMap = new HashMap<>();
		this.mStateArr = new ArrayList<>();
		this.mLetterArr = new ArrayList<>(mLetterMap.size());
		for(int i = 0; i < mLetterMap.size(); i ++) {
			this.mLetterArr.add(null);
		}
		for(Entry<LETTER, Integer> entry : mLetterMap.entrySet()) {
			assert entry.getValue() < mLetterMap.size();
			this.mLetterArr.set( entry.getValue(), entry.getKey());
		}
		computeInitialStates();
	}
	
	private IState getOrAddState(STATE str) {
		IState state = mStateMap.get(str);
		if(state == null) {
			state = addState();
			mStateMap.put(str, state);
			mStateArr.add(str);
			if(mInnerBuchi.isFinal(str)) this.setFinal(state.getId());
		}
		return state;
	}
	
	private void computeInitialStates() {
		// TODO Auto-generated method stub
		Iterable<STATE> states = mInnerBuchi.getInitialStates();
		for(STATE s : states) {
			IState state = getOrAddState(s);
			this.setInitial(state);
		}
	}

	
	private void computeStateSpace() {
		// TODO Auto-generated method stub
		Iterable<STATE> states = mInnerBuchi.getInitialStates();
		LinkedList<IState> walkList = new LinkedList<>();
		for(STATE s : states) {
			IState state = getOrAddState(s);
			this.setInitial(state);
			walkList.add(state);
			if(mInnerBuchi.isFinal(s)) this.setFinal(state);
		}
		
		BitSet visited = new BitSet();
		while(! walkList.isEmpty()) {
			IState curr = walkList.removeFirst();
			STATE s = mStateArr.get(curr.getId());
			if(mInnerBuchi.isFinal(s)) this.setFinal(curr);
			visited.set(curr.getId());
			Iterable<OutgoingInternalTransition<LETTER, STATE>> transIter = mInnerBuchi.internalSuccessors(s);
			for(OutgoingInternalTransition<LETTER, STATE> trans : transIter) {
				IState succ = getOrAddState(trans.getSucc());
				Integer letterId = mLetterMap.get(trans.getLetter()); 
				curr.addSuccessor(letterId, succ.getId());
				if(! visited.get(succ.getId())) {
					walkList.addFirst(succ);
				}
			}
		}
		
	}	
	
	// on-the-fly 
	@Override
	public BitSet getSuccessors(int state, int letter) {
		IState currState = getState(state);
		assert currState != null;
		
//		System.out.println("state " + state + " - " + letter + " ->");
		if(currState.isLetterVisited(letter)) {
			return currState.getSuccessors(letter);
		}
				
		LETTER letterStr = mLetterArr.get(letter);
		STATE currStateStr = mStateArr.get(state);
		
		BitSet succs = new BitSet();
		Iterable<OutgoingInternalTransition<LETTER, STATE>> transIter = mInnerBuchi.internalSuccessors(currStateStr, letterStr);
		for(OutgoingInternalTransition<LETTER, STATE> trans : transIter) {
			IState succ = getOrAddState(trans.getSucc());
			Integer letterId = mLetterMap.get(trans.getLetter());
			assert letterId == letter;
			// add states
			currState.addSuccessor(letterId, succ.getId());
			succs.set(succ.getId());
		}
//		System.out.println(" succs" + succs);

		return succs;
	}
	
	
	

}
