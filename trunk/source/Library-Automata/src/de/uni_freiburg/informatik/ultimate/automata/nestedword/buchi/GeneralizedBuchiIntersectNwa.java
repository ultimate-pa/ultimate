/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Generalized Buchi NWA intersection - first operand is generalized Buchi NWA and the second operand is Buchi NWA.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author liyong
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */

public class GeneralizedBuchiIntersectNwa<LETTER, STATE> implements IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final IBuchiIntersectStateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;

	private final Map<STATE, ProductState> mRes2prod = new HashMap<>();
	
	private final Map<STATE, Map<STATE, ProductState>> mFst2snd2res = new HashMap<>();
	
	private Set<STATE> mInitialStates;
	
	private int mAcceptanceSize;

	/**
	 * Constructor.
	 * 
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param stateFactory
	 *            state factory
	 * @throws AutomataLibraryException
	 *             if alphabets differ or operation was canceled
	 */
	public <FACTORY extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedBuchiIntersectNwa(
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand, final FACTORY stateFactory)
			throws AutomataLibraryException {
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}

		mStateFactory = stateFactory;
		mEmptyStackState = stateFactory.createEmptyStackState();
		mAcceptanceSize = mFstOperand.getAcceptanceSize() + 1;
	}

	private Set<STATE> constructInitialState() {
		final Set<STATE> initialStates = new HashSet<>();
		for (final STATE fst : mFstOperand.getInitialStates()) {
			for (final STATE snd : mSndOperand.getInitialStates()) {
				final STATE init = getOrConstructState(fst, snd);
				initialStates.add(init);
			}
		}
		return initialStates;
	}

	private STATE getOrConstructState(STATE fst, STATE snd) {
		Map<STATE, ProductState> snd2Res = mFst2snd2res.get(fst);
		if(snd2Res == null) {
			snd2Res = new HashMap<>();
			mFst2snd2res.put(fst, snd2Res);
		}
		ProductState prodState = snd2Res.get(snd);
		if(prodState == null) {
			final STATE res = mStateFactory.intersectBuchi(fst, snd, 1);
			prodState = new ProductState(fst, snd, res);
			prodState.setAcceptanceSet(computeAcceptance(fst, snd));
			snd2Res.put(snd, prodState);
			mRes2prod.put(res, prodState);
		}
		return prodState.getRes();
	}
	
	private Set<Integer> computeAcceptance(STATE fst, STATE snd) {
		final Set<Integer> acc = new HashSet<>();
		Set<Integer> fstAcc = mFstOperand.getAcceptanceLabels(fst);		
		for(Integer index : fstAcc) {
			acc.add(index);
		}
		int fstSize = mFstOperand.getAcceptanceSize();
		if(mSndOperand.isFinal(snd)) acc.add(fstSize);
		
		if(acc.isEmpty()) return Collections.emptySet();
		return acc;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		if (mInitialStates == null) {
			mInitialStates = constructInitialState();
		}
		return mInitialStates;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mFstOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mInitialStates.contains(state);
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
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		final STATE fst = mRes2prod.get(state).getFst();
		final STATE fstHier = mRes2prod.get(hier).getFst();
		return mFstOperand.lettersReturn(fst, fstHier);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		return internalSuccessors(mFstOperand.internalSuccessors(prod.getFst(), letter), prod);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		return internalSuccessors(mFstOperand.internalSuccessors(prod.getFst()), prod);
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> fstInternalSuccs, final ProductState prod) {
		final Collection<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : fstInternalSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndOperand
					.internalSuccessors(prod.getSnd(), letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingInternalTransition<>(letter, resSucc));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		return callSuccessors(mFstOperand.callSuccessors(prod.getFst(), letter), prod);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		return callSuccessors(mFstOperand.callSuccessors(prod.getFst()), prod);
	}

	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final Iterable<OutgoingCallTransition<LETTER, STATE>> fstCallSuccs, final ProductState prod) {
		final Collection<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingCallTransition<LETTER, STATE> fstTrans : fstCallSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingCallTransition<LETTER, STATE> sndTrans : mSndOperand.callSuccessors(prod.getSnd(),
					letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingCallTransition<>(letter, resSucc));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		final ProductState prodState = mRes2prod.get(state);
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessors(prodState.getFst(), fstHier, letter), prodState, hier,
				sndHier);
	}

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final Iterable<OutgoingReturnTransition<LETTER, STATE>> fstReturnSuccs, final ProductState prod,
			final STATE hier, final STATE sndHier) {
		final Collection<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingReturnTransition<LETTER, STATE> fstTrans : fstReturnSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingReturnTransition<LETTER, STATE> sndTrans : mSndOperand.returnSuccessors(prod.getSnd(),
					sndHier, letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingReturnTransition<>(hier, letter, resSucc));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		final ProductState prodState = mRes2prod.get(state);
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessorsGivenHier(prodState.getFst(), fstHier), prodState, hier,
				sndHier);
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}


	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return mRes2prod.size() + " states";
	}

	/**
	 * Product state for Generalized Buchi automata.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author liyong
	 */
	private class ProductState {
		private final STATE mFst;
		private final STATE mSnd;
		private final STATE mRes;
		private Set<Integer> mAcceptanceSet;

		ProductState(final STATE fst, final STATE snd, final STATE res) {
			mFst = fst;
			mSnd = snd;
			mRes = res;
		}

		public STATE getFst() {
			return mFst;
		}

		public STATE getSnd() {
			return mSnd;
		}

		public STATE getRes() {
			return mRes;
		}
		
		public void setAcceptanceSet(Set<Integer> acceptance) {
			mAcceptanceSet = acceptance;
		}
		
		public Set<Integer> getAcceptanceSet() {
			return mAcceptanceSet;
		}

		@Override
		public String toString() {
			return "<" + mFst.toString() + "," + mSnd.toString() + "," + mAcceptanceSet.toString() +  ">";
		}
	}

	@Override
	public boolean isFinal(STATE state, int index) {
		final Set<Integer> acceptanceSet = mRes2prod.get(state).getAcceptanceSet();
		if(acceptanceSet.isEmpty()) return false;
		return acceptanceSet.contains(index);
	}

	@Override
	public int getAcceptanceSize() {
		return mAcceptanceSize;
	}

	@Override
	public Set<Integer> getAcceptanceLabels(STATE state) {
		return mRes2prod.get(state).getAcceptanceSet();
	}
}

