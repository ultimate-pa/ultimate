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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

public class IntersectNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final StateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;
	
	private final Map<STATE,Map<STATE,ProductState>> mfst2snd2res =
			new HashMap<STATE,Map<STATE,ProductState>>();
	private final Map<STATE, ProductState> mres2prod = new HashMap<STATE, ProductState>();
	
	private final boolean mAssumeInSndNonFinalIsTrap;

	
	private Set<STATE> mInitialStates;
	
	
	public class ProductState {
		private final STATE mfst;
		private final STATE msnd;
		private final STATE mres;
		private final boolean mIsFinal;
		
		ProductState(STATE fst, STATE snd, STATE res, boolean isFinal) {
			mfst = fst;
			msnd = snd;
			mres = res;
			mIsFinal = isFinal;
		}

		public STATE getFst() {
			return mfst;
		}

		public STATE getSnd() {
			return msnd;
		}
		
		public STATE getRes() {
			return mres;
		}

		public boolean isFinal() {
			return mIsFinal;
		}
		
		@Override
		public String toString() {
			return "<" + mfst.toString() + "," + msnd.toString() + ">";
		}
		
	}
	
	
	public IntersectNwa(INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER, STATE> sndOperand, 
			StateFactory<STATE> sf, boolean assumeInSndNonFinalIsTrap) throws AutomataLibraryException {
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomaton.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(), "Unable to apply operation to automata with different alphabets.");
		}

		mStateFactory = sf;
		mAssumeInSndNonFinalIsTrap = assumeInSndNonFinalIsTrap;
		mEmptyStackState = mStateFactory.createEmptyStackState();
	}
	
	


	public Map<STATE, Map<STATE, ProductState>> getFst2snd2res() {
		return mfst2snd2res;
	}




	private Set<STATE> constructInitialState() {
		final Set<STATE> initialStates = new HashSet<STATE>();
		for (final STATE fst : mFstOperand.getInitialStates()) {
			for (final STATE snd : mSndOperand.getInitialStates()) {
				final STATE init = getOrConstructState(fst,snd);
				initialStates.add(init);
			}
		}
		return initialStates;
	}
	
	private STATE getOrConstructState(STATE fst, STATE snd) {
		Map<STATE, ProductState> snd2res = mfst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			mfst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			final STATE res = mStateFactory.intersection(fst, snd);
			final boolean isFinal = mFstOperand.isFinal(fst) && mSndOperand.isFinal(snd);
			prod = new ProductState(fst, snd, res, isFinal);
			snd2res.put(snd, prod);
			mres2prod.put(res, prod);
		}
		return prod.getRes();
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
	public boolean isInitial(STATE state) {
		if (mInitialStates == null) {
			mInitialStates = constructInitialState();
		}
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return mres2prod.get(state).isFinal();
	}

	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		final STATE fst = mres2prod.get(state).getFst(); 
		return mFstOperand.lettersInternal(fst);
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		final STATE fst = mres2prod.get(state).getFst(); 
		return mFstOperand.lettersCall(fst);
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		final STATE fst = mres2prod.get(state).getFst(); 
		return mFstOperand.lettersReturn(fst);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		final ProductState prod = mres2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return internalSuccessors(mFstOperand.internalSuccessors(fst,letter), snd);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		final ProductState prod = mres2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return internalSuccessors(mFstOperand.internalSuccessors(fst), snd);
	}


	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			Iterable<OutgoingInternalTransition<LETTER, STATE>> fstInternalSuccs,
			STATE snd) {
		final Collection<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : fstInternalSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndOperand.internalSuccessors(snd, letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}
	


	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		final ProductState prod = mres2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return callSuccessors(mFstOperand.callSuccessors(fst,letter), snd);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		final ProductState prod = mres2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return callSuccessors(mFstOperand.callSuccessors(fst), snd);
	}


	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			Iterable<OutgoingCallTransition<LETTER, STATE>> fstCallSuccs,
			STATE snd) {
		final Collection<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		for (final OutgoingCallTransition<LETTER, STATE> fstTrans : fstCallSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingCallTransition<LETTER, STATE> sndTrans : mSndOperand.callSuccessors(snd, letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingCallTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, STATE hier, LETTER letter) {
		final ProductState prodState = mres2prod.get(state);
		final STATE fstState = prodState.getFst();
		final STATE sndState = prodState.getSnd();
		final ProductState prodHier = mres2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessors(
							fstState, fstHier, letter), hier, sndState, sndHier);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		final ProductState prodState = mres2prod.get(state);
		final STATE fstState = prodState.getFst();
		final STATE sndState = prodState.getSnd();
		final ProductState prodHier = mres2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessorsGivenHier(
							fstState, fstHier), hier, sndState, sndHier);
	}


	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			Iterable<OutgoingReturnTransition<LETTER, STATE>> fstReturnSuccs,
			STATE hier, STATE sndState, STATE sndHier) {
		final Collection<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (final OutgoingReturnTransition<LETTER, STATE> fstTrans : fstReturnSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingReturnTransition<LETTER, STATE> sndTrans : 
						mSndOperand.returnSuccessors(sndState, sndHier,  letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingReturnTransition<LETTER, STATE>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public int size() {
		return mres2prod.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return getInternalAlphabet();
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}


}
