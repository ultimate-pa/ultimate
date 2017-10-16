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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;

/**
 * Compute Intersection of two Buchi automta and the result is Buchi automaton
 * */
public class BuchiWaIntersection extends BuchiWa implements IBuchiWaIntersection {

	private final IBuchiWa mFstOperand;
	private final IBuchiWa mSndOperand;
		
	private final TObjectIntMap<ProductState> mState2Int = new TObjectIntHashMap<>();
	
	public BuchiWaIntersection(IBuchiWa fstOp, IBuchiWa sndOp) {
		super(fstOp.getAlphabetSize());
		assert fstOp.getAlphabetSize() == sndOp.getAlphabetSize();
		this.mFstOperand = fstOp;
		this.mSndOperand = sndOp;
		computeInitialStates();
	}
	
	
	protected ProductState getOrAddState(int fst, int snd, TrackNumber track) {
		ProductState state = new ProductState(this, 0, fst, snd, track);
		if(mState2Int.containsKey(state)) {
			return (ProductState) getState(mState2Int.get(state));
		}
		// add new state
		ProductState newState = new ProductState(this, getStateSize(), fst, snd, track);
		int id = this.addState(newState);
		mState2Int.put(newState, id);
		// whether it is accepting state
		final boolean isFinal = mFstOperand.isFinal(fst) && track.isOne();
		if(isFinal) setFinal(id);
		return newState;
	}

	private void computeInitialStates() {
		IntSet fstInits = mFstOperand.getInitialStates();
		IntSet sndInits = mSndOperand.getInitialStates();
		
		IntIterator fstIter = fstInits.iterator();
		while(fstIter.hasNext()) {
			int fst = fstIter.next();
			IntIterator sndIter = sndInits.iterator();
			while(sndIter.hasNext()) {
				int snd = sndIter.next();
				ProductState state = getOrAddState(fst, snd, TrackNumber.TRACK_ONE);		
				this.setInitial(state);
			}
		}
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
	
	// ------------------------------------ 
	class ProductState extends StateWa implements IProductState {

		private final int mFstState;
		private final int mSndState;
		private final TrackNumber mTrack;
		private TrackNumber mSuccTrack = null;
		
		public ProductState(BuchiWaIntersection buchi
				, int id, int fstState, int sndState, TrackNumber track) {
			super(id);
			this.mFstState = fstState;
			this.mSndState = sndState;
			this.mTrack = track;
		}
		
		@Override
		public boolean equals(Object obj) {
			if(this == obj) return true;
			if(!(obj instanceof ProductState)) {
				return false;
			}
			ProductState other = (ProductState)obj;
			return this.contentEq(other);
		}
		
		@Override
		public String toString() {
			return "(" + mFstState + "," + mSndState + "):" + mTrack;
		}
		
		int hashCode = 1;
		boolean hasCode = false;
		@Override
		public int hashCode() {
			if(hasCode) return hashCode;
			else {
				hasCode = true;
		        final int prime = 31;
		        hashCode = prime * hashCode + mFstState;
		        hashCode = prime * hashCode + mSndState;
				hashCode += mTrack == TrackNumber.TRACK_ONE ? 1 : 2;
			}
			return hashCode;
		}
		
		public int getFstState() {
			return mFstState;
		}
		
		public int getSndState() {
			return mSndState;
		}
			
		private IntSet visitedLetters = UtilIntSet.newIntSet();

		@Override
		public IntSet getSuccessors(int letter) {
			if(visitedLetters.get(letter)) {
				return super.getSuccessors(letter);
			}
			visitedLetters.set(letter);
			
			// compute successors
			IntSet fstSuccs = mFstOperand.getState(mFstState).getSuccessors(letter);
			IntSet sndSuccs = mSndOperand.getState(mSndState).getSuccessors(letter);
			final IntSet succs = UtilIntSet.newIntSet();
			for(final Integer fstSucc : fstSuccs.iterable()) {
				for(final Integer sndSucc : sndSuccs.iterable()) {
					TrackNumber succTrack = getSuccStateTrack();
					// pair (X, Y)
					ProductState succ = getOrAddState(fstSucc, sndSucc, succTrack);                
					this.addSuccessor(letter, succ.getId());
					succs.set(succ.getId());
				}
			}

			return succs;
		}

		@Override
		public TrackNumber getTrackNumber() {
			return mTrack;
		}

		@Override
		public TrackNumber getSuccStateTrack() {
			if(mSuccTrack == null) {
				mSuccTrack = this.getSuccStateTrack(
                               mFstOperand.isFinal(mFstState)
                               , mSndOperand.isFinal(mSndState));
			}
			return mSuccTrack;
		}

	}

	@Override
	public String getOperationName() {
		return "WaIntersection";
	}

}
