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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.Acc;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.AccGenBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;



/**
 * Compute Intersection of two Buchi automta and the result is generalized Buchi automaton
 * */
public class GeneralizedBuchiIntersection extends BuchiWa implements IBuchiWaIntersection {

	private final IBuchiWa mFstOperand;
	private final IBuchiWa mSndOperand;
	
	private final TObjectIntMap<GeneralizedState> mState2Int = new TObjectIntHashMap<>();
		
	public GeneralizedBuchiIntersection(IBuchiWa fstOp, IBuchiWa sndOp) {
		super(fstOp.getAlphabetSize());
		this.mFstOperand = fstOp;
		this.mSndOperand = sndOp;
		computeInitialStates();
	}
	
	@Override
	public IBuchiWa getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public IBuchiWa getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public IBuchiWa getResult() {
		return this;
	}
	
	// take care of the acceptance
	protected GeneralizedState addState(int left, int right) {
		GeneralizedState state = new GeneralizedState(this, 0);
		state.setPairs(left, right);		
		if(mState2Int.containsKey(state)) {
			return (GeneralizedState) getState(mState2Int.get(state));
		}else {
			GeneralizedState newState = new GeneralizedState(this, getStateSize());
			newState.setPairs(left, right);
			int id = this.addState(newState);
			mState2Int.put(newState, id);
			getAcceptance().setAcc(newState);
			return newState;
		}
	}

	private void computeInitialStates() {
		// first compute initial states
		IntSet fstInits = mFstOperand.getInitialStates();
		IntSet sndInits = mSndOperand.getInitialStates();
		for(final Integer fst : fstInits.iterable()) {
			for(final Integer snd : sndInits.iterable()) {
				GeneralizedState state = addState(fst, snd);				
				this.setInitial(state);
			}
		}
	}
	
	@Override
	public AccBuchiIntersection getAcceptance() {
		if(acc == null) {
			acc = new AccBuchiIntersection();
		}
		return (AccBuchiIntersection)acc;
	}
	
	private class AccBuchiIntersection extends AccGenBuchi {

		public AccBuchiIntersection() {
			super(mFstOperand.getAcceptance().getAccSize() + mSndOperand.getAcceptance().getAccSize());
		}
		
		protected void setAcc(GeneralizedState state) {
			IntSet result = UtilIntSet.newIntSet(); 
			result.or(mFstOperand.getAcceptance().getLabels(state.getLeft()));
			for(int label : mSndOperand.getAcceptance().getLabels(state.getRight()).iterable()) {
				result.set(mFstOperand.getAcceptance().getAccSize() + label);
			}
			this.setLabel(state.getId(), result);
		}
	}

	@Override
	public String getOperationName() {
		return "GenWaIntersection";
	}

}
