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
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiGeneral;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.BuchiComplementSDBA;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.IBuchiComplement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.StateNCSB;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public abstract class BuchiInclusion implements IBuchiInclusion{
	
	protected final IBuchi mFstOperand;
	protected final IBuchi mSndOperand;
	protected final BuchiComplementSDBA mSndComplement;
	
	protected final IBuchi mResult;
	// use antichain to accelerate inclusion check
//	protected final TaskInclusion mTask;
	
	protected BuchiInclusion(IBuchi fstOp, IBuchi sndOp) {
//		this.mTask = task;
		this.mFstOperand = fstOp;
		this.mSndOperand = sndOp;
		this.mSndComplement = new BuchiComplementSDBA(sndOp);
		this.mResult = new BuchiGeneral(fstOp.getAlphabetSize());
//		this.mTask.setOperation(this);
		computeInitalStates();
	}
	
	private void computeInitalStates() {
		IntIterator fstIter = mFstOperand.getInitialStates().iterator();
		while(fstIter.hasNext()) {
		    int fst = fstIter.next();
		    IntIterator sndIter = mSndComplement.getInitialStates().iterator();
		    while(sndIter.hasNext()) {
		    	int snd = sndIter.next();
				StateNCSB sndState = (StateNCSB)mSndComplement.getState(snd);
				InclusionPairNCSB pair = new InclusionPairNCSB(fst, sndState);
				IState state = getOrAddState(pair);
				mResult.setInitial(state);
			}
		}
	}

	protected final Map<InclusionPairNCSB, IState> mPairStateMap = new HashMap<>();
	protected final BitSet mFstFinalStates = new BitSet();
	protected final BitSet mSndFinalStates = new BitSet();
	protected final List<InclusionPairNCSB> mPairNCSBArray = new ArrayList<>();
	
	protected IState getOrAddState(InclusionPairNCSB pair) {
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
	
//	protected abstract boolean isValidPair(InclusionPairNCSB pair);
	
	
	@Override
	public IBuchi getFstBuchi() {
		return mFstOperand;
	}
	
	@Override
	public IBuchi getSndBuchi() {
		return mSndOperand;
	}

	@Override
	public IBuchiComplement getSndBuchiComplement() {
		return mSndComplement;
	}
	
	@Override
	public IBuchi getBuchiDifference() {
		return mResult;
	}

}
