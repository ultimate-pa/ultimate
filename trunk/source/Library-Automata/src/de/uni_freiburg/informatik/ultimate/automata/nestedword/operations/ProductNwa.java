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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * On-the-fly intersection of two nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class ProductNwa<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	// TODO 2017-06-23 Christian: this field is only present while automata provide their state factories
	private final IEmptyStackStateFactory<STATE> mStateFactory;

	private final STATE mEmptyStackState;

	private final Map<STATE, Map<STATE, ProductState>> mFst2snd2res = new HashMap<>();
	private final Map<STATE, ProductState> mRes2prod = new HashMap<>();

	private final boolean mAssumeInSndNonFinalIsTrap;

	private Set<STATE> mInitialStates;

	/**
	 * @param fstOperand
	 *            First operand.
	 * @param sndOperand
	 *            second operand
	 * @param emptyStackStateFactory
	 *            state factory for creating empty stack
	 * @param assumeInSndNonFinalIsTrap
	 *            assume that in the second operand a non-final state is a trap (i.e., whenever we reach a non-final
	 *            state we can never go back to a final state. 2016-11-19 Matthias: I don't know if "trap" is well-known
	 *            terminology or a term that we invented.)
	 * @throws AutomataLibraryException
	 *             if alphabets differ
	 */
	protected ProductNwa(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand,
			final IEmptyStackStateFactory<STATE> emptyStackStateFactory, final boolean assumeInSndNonFinalIsTrap)
			throws AutomataLibraryException {
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}

		mStateFactory = emptyStackStateFactory;
		mAssumeInSndNonFinalIsTrap = assumeInSndNonFinalIsTrap;
		mEmptyStackState = emptyStackStateFactory.createEmptyStackState();
	}

	public Map<STATE, Map<STATE, ProductState>> getFst2snd2res() {
		return mFst2snd2res;
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

	private STATE getOrConstructState(final STATE fst, final STATE snd) {
		Map<STATE, ProductState> snd2res = mFst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<>();
			mFst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			prod = createProductState(fst, snd);
			snd2res.put(snd, prod);
			mRes2prod.put(prod.getRes(), prod);
		}
		return prod.getRes();
	}

	/**
	 * @param fst
	 *            State in first operand.
	 * @param snd
	 *            state in second operand
	 * @return product state
	 */
	protected abstract ProductState createProductState(final STATE fst, final STATE snd);

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
		if (mInitialStates == null) {
			mInitialStates = constructInitialState();
		}
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
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		final STATE fst = mRes2prod.get(state).getFst();
		final STATE fstHier = mRes2prod.get(hier).getFst();
		return mFstOperand.lettersReturn(fst, fstHier);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return internalSuccessors(mFstOperand.internalSuccessors(fst, letter), snd);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return internalSuccessors(mFstOperand.internalSuccessors(fst), snd);
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> fstInternalSuccs, final STATE snd) {
		final Collection<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : fstInternalSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndOperand.internalSuccessors(snd,
					letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingInternalTransition<>(letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		final ProductState prod = mRes2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return callSuccessors(mFstOperand.callSuccessors(fst, letter), snd);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		final ProductState prod = mRes2prod.get(state);
		final STATE fst = prod.getFst();
		final STATE snd = prod.getSnd();
		return callSuccessors(mFstOperand.callSuccessors(fst), snd);
	}

	private Iterable<OutgoingCallTransition<LETTER, STATE>>
			callSuccessors(final Iterable<OutgoingCallTransition<LETTER, STATE>> fstCallSuccs, final STATE snd) {
		final Collection<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingCallTransition<LETTER, STATE> fstTrans : fstCallSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingCallTransition<LETTER, STATE> sndTrans : mSndOperand.callSuccessors(snd, letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingCallTransition<>(letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		final ProductState prodState = mRes2prod.get(state);
		final STATE fstState = prodState.getFst();
		final STATE sndState = prodState.getSnd();
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessors(fstState, fstHier, letter), hier, sndState, sndHier);
	}

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final Iterable<OutgoingReturnTransition<LETTER, STATE>> fstReturnSuccs, final STATE hier,
			final STATE sndState, final STATE sndHier) {
		final Collection<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingReturnTransition<LETTER, STATE> fstTrans : fstReturnSuccs) {
			final LETTER letter = fstTrans.getLetter();
			for (final OutgoingReturnTransition<LETTER, STATE> sndTrans : mSndOperand.returnSuccessors(sndState,
					sndHier, letter)) {
				final STATE fstSucc = fstTrans.getSucc();
				final STATE sndSucc = sndTrans.getSucc();
				if (mAssumeInSndNonFinalIsTrap && !mSndOperand.isFinal(sndSucc)) {
					continue;
				}
				final STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingReturnTransition<>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		final ProductState prodState = mRes2prod.get(state);
		final STATE fstState = prodState.getFst();
		final STATE sndState = prodState.getSnd();
		final ProductState prodHier = mRes2prod.get(hier);
		final STATE fstHier = prodHier.getFst();
		final STATE sndHier = prodHier.getSnd();
		return returnSuccessors(mFstOperand.returnSuccessorsGivenHier(fstState, fstHier), hier, sndState, sndHier);
	}

	@Override
	public int size() {
		return mRes2prod.size();
	}

	@Override
	public String sizeInformation() {
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	/**
	 * State of the product construction.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public class ProductState {
		private final STATE mFst;
		private final STATE mSnd;
		private final STATE mRes;
		private final boolean mIsFinal;

		ProductState(final STATE fst, final STATE snd, final STATE res, final boolean isFinal) {
			mFst = fst;
			mSnd = snd;
			mRes = res;
			mIsFinal = isFinal;
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

		public boolean isFinal() {
			return mIsFinal;
		}

		@Override
		public String toString() {
			return "<" + mFst.toString() + "," + mSnd.toString() + ">";
		}
	}
}
