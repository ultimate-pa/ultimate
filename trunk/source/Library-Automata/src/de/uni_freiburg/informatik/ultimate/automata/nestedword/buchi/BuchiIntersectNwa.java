/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

public class BuchiIntersectNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final StateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;
	
	private final Map<STATE,Map<STATE,ProductState>> mTrack1_fst2snd2res = new HashMap<>();
	private final Map<STATE,Map<STATE,ProductState>> mTrack2_fst2snd2res = new HashMap<>();
	private final Map<STATE, ProductState> mRes2prod = new HashMap<STATE, ProductState>();
	
	private Set<STATE> mInitialStates;
	
	
	private class ProductState {
		private final STATE mFst;
		private final STATE mSnd;
		private final byte mTrack;
		private final STATE mRes;
		private final boolean mIsFinal;
		
		ProductState(final STATE fst, final STATE snd, final byte track, final STATE res, final boolean isFinal) {
			mFst = fst;
			mSnd = snd;
			mTrack = track;
			mRes = res;
			mIsFinal = isFinal;
		}

		public STATE getFst() {
			return mFst;
		}

		public STATE getSnd() {
			return mSnd;
		}
		
		public byte getTrack() {
			return mTrack;
		}
		
		public STATE getRes() {
			return mRes;
		}

		public boolean isFinal() {
			return mIsFinal;
		}
		
		@Override
		public String toString() {
			return "<" + mFst.toString() + "," + mSnd.toString() + " " + mTrack + ">";
		}
		
	}
	
	
	public BuchiIntersectNwa(final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand,
			final StateFactory<STATE> sf) throws AutomataLibraryException {
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomaton.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}

		mStateFactory = sf;
		mEmptyStackState = mStateFactory.createEmptyStackState();
	}


	private Set<STATE> constructInitialState() {
		final Set<STATE> initialStates = new HashSet<STATE>();
		for (final STATE fst : mFstOperand.getInitialStates()) {
			for (final STATE snd : mSndOperand.getInitialStates()) {
				final STATE init = getOrConstructStateOnTrack1(fst,snd);
				initialStates.add(init);
			}
		}
		return initialStates;
	}
	
	private STATE getOrConstructStateOnTrack1(final STATE fst, final STATE snd) {
		Map<STATE, ProductState> snd2res = mTrack1_fst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			mTrack1_fst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			final STATE res = mStateFactory.intersectBuchi(fst, snd, 1);
			final boolean isFinal = mFstOperand.isFinal(fst);
			prod = new ProductState(fst, snd, (byte) 1, res, isFinal);
			snd2res.put(snd, prod);
			mRes2prod.put(res, prod);
		}
		return prod.getRes();
	}
	
	private STATE getOrConstructStateOnTrack2(final STATE fst, final STATE snd) {
		Map<STATE, ProductState> snd2res = mTrack2_fst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			mTrack2_fst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			final STATE res = mStateFactory.intersectBuchi(fst, snd, 2);
			prod = new ProductState(fst, snd, (byte) 2, res, false);
			snd2res.put(snd, prod);
			mRes2prod.put(res, prod);
		}
		return prod.getRes();
	}
	
	private byte getSuccTrack(final ProductState prodState) {
		byte succTrack;
			if (prodState.getTrack() == 1) {
				if (mFstOperand.isFinal(prodState.getFst()) && !mSndOperand.isFinal(prodState.getSnd())) {
					succTrack = 2;
				} else {
					succTrack = 1;
				}
			} else {
				assert (prodState.getTrack() == 2);
				if (mSndOperand.isFinal(prodState.getSnd())) {
					succTrack = 1;
				} else {
					succTrack = 2;
				}
			}
		return succTrack;
	}
	
	
	
	@Override
	public Iterable<STATE> getInitialStates() {
		if (mInitialStates == null) {
			mInitialStates = constructInitialState();
		}
		return mInitialStates;
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mFstOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mFstOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mFstOperand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mRes2prod.get(state).isFinal();
	}

	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		final STATE fst = mRes2prod.get(state).getFst();
		return mFstOperand.lettersInternal(fst);
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		final STATE fst = mRes2prod.get(state).getFst();
		return mFstOperand.lettersCall(fst);
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		final STATE fst = mRes2prod.get(state).getFst();
		return mFstOperand.lettersReturn(fst);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		return internalSuccessors(mFstOperand.internalSuccessors(prod.getFst(),letter), prod);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		return internalSuccessors(mFstOperand.internalSuccessors(prod.getFst()), prod);
	}


	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> fstInternalSuccs,
			final ProductState prod) {
		final Collection<OutgoingInternalTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : fstInternalSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> sndTrans :
					mSndOperand.internalSuccessors(prod.getSnd(), letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				final byte succTrack = getSuccTrack(prod);
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}
	


	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		return callSuccessors(mFstOperand.callSuccessors(prod.getFst(),letter), prod);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		return callSuccessors(mFstOperand.callSuccessors(prod.getFst()), prod);
	}


	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final Iterable<OutgoingCallTransition<LETTER, STATE>> fstCallSuccs,
			final ProductState prod) {
		final Collection<OutgoingCallTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		for (final OutgoingCallTransition<LETTER, STATE> fstTrans : fstCallSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingCallTransition<LETTER, STATE> sndTrans :
						mSndOperand.callSuccessors(prod.getSnd(), letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				final byte succTrack = getSuccTrack(prod);
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingCallTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		final ProductState prodState = mRes2prod.get(state);
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessors(
				prodState.getFst(), fstHier, letter), prodState, hier, sndHier);
	}


	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final Iterable<OutgoingReturnTransition<LETTER, STATE>> fstReturnSuccs,
			final ProductState prod, final STATE hier, final STATE sndHier) {
		final Collection<OutgoingReturnTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (final OutgoingReturnTransition<LETTER, STATE> fstTrans : fstReturnSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingReturnTransition<LETTER, STATE> sndTrans :
						mSndOperand.returnSuccessors(prod.getSnd(), sndHier,  letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				final byte succTrack = getSuccTrack(prod);
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingReturnTransition<LETTER, STATE>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		final ProductState prodState = mRes2prod.get(state);
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessorsGivenHier(
							prodState.getFst(), fstHier), prodState, hier, sndHier);
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return getInternalAlphabet();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}


}
