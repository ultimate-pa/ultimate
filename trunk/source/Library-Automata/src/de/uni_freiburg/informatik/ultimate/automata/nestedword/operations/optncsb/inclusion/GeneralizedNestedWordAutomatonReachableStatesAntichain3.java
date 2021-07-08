/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;

/**
 * A nested word automaton with reachable states information.
 *
 * @author Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class GeneralizedNestedWordAutomatonReachableStatesAntichain3<LETTER, STATE>
		extends AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> {

	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> mSndOperand;

	private final Map<STATE, ProductStateContainer> mStates = new HashMap<>();

	private final Map<STATE, Map<STATE, ProductStateContainer>> mFst2snd2res = new HashMap<>();

	private final ReachableStatesComputation mReach;

	private final IBuchiIntersectStateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;
	private final int mAcceptanceSize;
	private static int mNumber = 0;

	public <FACTORY extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedNestedWordAutomatonReachableStatesAntichain3(
			final AutomataLibraryServices services,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> sndOperand, final FACTORY stateFactory)
			throws AutomataLibraryException {
		super(services, fstOperand.getVpAlphabet());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}
		mStateFactory = stateFactory;
		mEmptyStackState = mStateFactory.createEmptyStackState();
		mDownStates.add(mEmptyStackState);
		mAcceptanceSize = fstOperand.getAcceptanceSize() + 1;
		try {
			mReach = new ReachableStatesComputation();
			new RemoveUnusedStates<>(mServices, this);
			mFinalStates.clear();
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Error | RuntimeException e) {
			throw e;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(stateContainerInformation());
		}

		final boolean dumpFile = true;
		if (dumpFile) {
			mNumber++;
			GeneralizedBuchiToBuchi<LETTER, STATE> gba2ba = new GeneralizedBuchiToBuchi<>(stateFactory, mFstOperand);
			new AutomatonDefinitionPrinter<String, String>(mServices, "Program", "./program" + mNumber, Format.BA, "",
					gba2ba);
			new AutomatonDefinitionPrinter<String, String>(mServices, "Complement", "./complement" + mNumber, Format.BA,
					"", mSndOperand);
			gba2ba = new GeneralizedBuchiToBuchi<>(stateFactory, this);
			new AutomatonDefinitionPrinter<String, String>(mServices, "Difference", "./difference" + mNumber, Format.BA,
					"", gba2ba);
		}
	}

	@Override
	protected StateContainer<LETTER, STATE> getStateContainer(final STATE state) {
		return mStates.get(state);
	}

	private String stateContainerInformation() {
		return mStates.size() + " StateContainers ";
	}

	@Override
	public Boolean isEmpty() {
		return mReach.mIsEmpty;
	}

	private NestedLassoRun<LETTER, STATE> mLasso = null;

	// have to use information in tarjan
	@Override
	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataOperationCanceledException {
		if (mReach.mIsEmpty) {
			return null;
		}
		// construct lasso run
		if (mLasso == null) {
			for (final List<STATE> scc : mReach.mSccList) {
				final LassoConstructor<LETTER, STATE> lc = new LassoConstructor<>(mServices, this, scc);
				final NestedLassoRun<LETTER, STATE> lasso = lc.getNestedLassoRun();
				if (mLasso == null || mLasso.getStem().getLength()
						+ mLasso.getLoop().getLength() > lasso.getStem().getLength() + lasso.getLoop().getLength()) {
					mLasso = lasso;
				}
			}
		}
		return mLasso;
	}

	@Override
	protected void removeStates(final STATE state) {

	}

	/**
	 * We use Antichain to reduce some states in reachability analysis
	 */
	class ReachableStatesComputation {

		private int mDepth;
		private final Stack<AsccPair<LETTER, STATE>> mRootsStack;
		private final Map<STATE, Integer> mDfsNum;
		private final Stack<STATE> mActiveStack;
		private final List<LinkedList<STATE>> mSccList;
		private Boolean mIsEmpty = null;

		private final Antichain mAntichain; // some kind of empty sets

		public ReachableStatesComputation() throws AutomataOperationCanceledException {
			mNumberOfConstructedStates = 0;
			computeInitialStates();

			mDepth = 0;
			mDfsNum = new HashMap<>();
			mActiveStack = new Stack<>();
			mSccList = new ArrayList<>();
			mRootsStack = new Stack<>();
			mAntichain = new Antichain();

			// initialize
			for (final STATE state : getInitialStates()) {
				if (!mDfsNum.containsKey(state)) {
					construct(state);
				}
			}

			if (mIsEmpty == null) {
				mIsEmpty = true;
			}

			for (final STATE state : mAntichain.getStates()) {
				mStates.remove(state);
			}

		}

		private void computeInitialStates() {
			for (final STATE fst : mFstOperand.getInitialStates()) {
				for (final STATE snd : mSndOperand.getInitialStates()) {
					final STATE init = getOrConstructState(fst, snd);
					mInitialStates.add(init);
				}
			}
		}

		/**
		 * Use the kind of style by Matthias to get or construct new state
		 */
		private STATE getOrConstructState(final STATE fst, final STATE snd) {
			Map<STATE, ProductStateContainer> snd2Res = mFst2snd2res.get(fst);
			if (snd2Res == null) {
				snd2Res = new HashMap<>();
				mFst2snd2res.put(fst, snd2Res);
			}
			ProductStateContainer prodStateCont = snd2Res.get(snd);
			if (prodStateCont == null) {
				final STATE res = mStateFactory.intersectBuchi(fst, snd, 1);
				final ProductState prodState = new ProductState(fst, snd, res);
				prodState.setAcceptanceSet(computeAcceptance(fst, snd));
				prodStateCont = new ProductStateContainer(res, prodState);
				snd2Res.put(snd, prodStateCont);
				mStates.put(res, prodStateCont);
				if (!prodState.mAcceptanceSet.isEmpty()) {
					mFinalStates.add(res);
				}
				mNumberOfConstructedStates++;
			}
			return prodStateCont.getState();
		}

		private Set<Integer> computeAcceptance(final STATE fst, final STATE snd) {
			final Set<Integer> acc = new HashSet<>();
			final Set<Integer> fstAcc = mFstOperand.getAcceptanceLabels(fst);
			acc.addAll(fstAcc);
			final int fstSize = mFstOperand.getAcceptanceSize();
			if (mSndOperand.isFinal(snd)) {
				acc.add(fstSize);
			}

			if (acc.isEmpty()) {
				return Collections.emptySet();
			}
			return acc;
		}

		// here the local variable is_nonempty is useful to identify states which have empty languages
		// empty is Antichain to store empty states (have empty languages)
		//
		boolean construct(final STATE state) throws AutomataOperationCanceledException {

			final ProductStateContainer prodStateCont = mStates.get(state);
			boolean notEmpty = false;
			mDepth++;
			mDfsNum.put(state, mDepth);
			mActiveStack.push(state);
			mRootsStack.push(new AsccPair<>(state, prodStateCont.mProdState.getAcceptanceSet()));

			for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : mFstOperand
					.internalSuccessors(prodStateCont.mProdState.getFst())) {
				for (final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndOperand
						.internalSuccessors(prodStateCont.mProdState.getSnd(), fstTrans.getLetter())) {
					if (!getServices().getProgressAwareTimer().continueProcessing()) {
						final RunningTaskInfo rti = constructRunningTaskInfo();
						throw new AutomataOperationCanceledException(rti);
					}
					final STATE succState = getOrConstructState(fstTrans.getSucc(), sndTrans.getSucc());
					final ProductState succProd = mStates.get(succState).getProd();
					prodStateCont
							.addInternalOutgoing(new OutgoingInternalTransition<>(fstTrans.getLetter(), succState));
					mStates.get(succState)
							.addInternalIncoming(new IncomingInternalTransition<>(state, fstTrans.getLetter()));
					if (mAntichain.covers(succProd)) {
						continue;
					}
					if (!mDfsNum.containsKey(succState)) {
						// whether there is accepting loop in the following
						// notEmpty |= construct(succState);
						notEmpty = construct(succState) || notEmpty;
					} else if (mActiveStack.contains(succState)) {
						final Set<Integer> labels = new HashSet<>();
						STATE topState;
						do {
							final AsccPair<LETTER, STATE> pair = mRootsStack.pop();
							topState = pair.mState;
							labels.addAll(pair.mLabels);
							if (labels.size() == getAcceptanceSize()) {
								notEmpty = true;
							}
						} while (mDfsNum.get(topState) > mDfsNum.get(succState));
						mRootsStack.push(new AsccPair<>(topState, labels));
					}
				}
			}
			if (mRootsStack.peek().mState.equals(state)) {
				final AsccPair<LETTER, STATE> pair = mRootsStack.pop(); // remove the root
				STATE topState;
				final LinkedList<STATE> scc = new LinkedList<>();
				do {
					if (mActiveStack.isEmpty()) {
						break;
					}
					// pop all states in the same SCC
					topState = mActiveStack.pop();
					scc.add(topState);
					if (!notEmpty) { // empty language
						mAntichain.addState(mStates.get(topState).mProdState);
						// // remove all incoming transitions to topState
						final ProductStateContainer cont = mStates.get(topState);
						final Set<STATE> pred = new HashSet<>();
						for (final IncomingInternalTransition<LETTER, STATE> trans : cont.internalPredecessors()) {
							final ProductStateContainer predCont = mStates.get(trans.getPred());
							predCont.removeSuccessor(topState);
							pred.add(trans.getPred());
						}
						cont.removePredecessors(pred);
					}
				} while (!topState.equals(state));
				// whether there is accepting loop
				if (pair.mLabels.size() == getAcceptanceSize()) {
					if (scc.size() > 1 || prodStateCont.hashSelfloop()) {
						mSccList.add(scc);
						mIsEmpty = false;
					}
				}
			}
			return notEmpty;
		}
	}

	private class AsccPair<LETTER, STATE> {
		final STATE mState;
		final Set<Integer> mLabels;

		AsccPair(final STATE state, final Set<Integer> labels) {
			this.mState = state;
			this.mLabels = labels;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof AsccPair)) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final AsccPair<LETTER, STATE> other = (AsccPair<LETTER, STATE>) obj;
			return mState.equals(other.mState) && mLabels.equals(other.mLabels);
		}

		@Override
		public int hashCode() {
			return mState.hashCode() + mLabels.hashCode();
		}
	}

	// -----------------------------------------------------------

	private AutomataLibraryServices getServices() {
		return mServices;
	}

	private RunningTaskInfo constructRunningTaskInfo() {
		final String taskDescription = constructRunningTaskInfoMessage(mNumberOfConstructedStates, getClass());
		return new RunningTaskInfo(getClass(), taskDescription);
	}

	@Override
	public Set<STATE> getStates() {
		return mStates.keySet();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mFinalStates);
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		return mStates.get(state).lettersInternalIncoming();
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return mStates.get(succ).internalPredecessors(letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return mStates.get(succ).internalPredecessors();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return mStates.get(state).internalSuccessors(letter);
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return size() + " states";
	}

	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mInitialStates.contains(state);
	}

	@Override
	public int getAcceptanceSize() {
		return mAcceptanceSize;
	}

	@Override
	public boolean isFinal(final STATE state, final int index) {
		return mStates.get(state).mProdState.mAcceptanceSet.contains(index);
	}

	@Override
	public Set<Integer> getAcceptanceLabels(final STATE state) {
		return mStates.get(state).mProdState.mAcceptanceSet;
	}

	@Override
	public boolean isFinal(final STATE state) {
		return !getAcceptanceLabels(state).isEmpty();
	}

	// ------------------------------------------------------
	private class ProductStateContainer extends StateContainer<LETTER, STATE> {
		ProductState mProdState;

		public ProductStateContainer(final STATE state, final ProductState prod) {
			super(state);
			mProdState = prod;
		}

		ProductState getProd() {
			return mProdState;
		}
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

		public void setAcceptanceSet(final Set<Integer> acceptance) {
			mAcceptanceSet = acceptance;
		}

		public boolean coveredBy(final ProductState other) {
			return mFst.equals(other.mFst) && mSndOperand.coveredBy(mSnd, other.mSnd);
		}

		public Set<Integer> getAcceptanceSet() {
			return mAcceptanceSet;
		}

		@Override
		public String toString() {
			return "<" + mFst.toString() + "," + mSnd.toString() + "," + mAcceptanceSet.toString() + ">";
		}
	}

	// ----------------------------------------------------
	private class Antichain {
		private final Map<STATE, List<ProductState>> mResStateMap;

		public Antichain() {
			mResStateMap = new HashMap<>();
		}

		Set<STATE> getStates() {
			return mResStateMap.keySet();
		}

		public boolean addState(final ProductState state) {

			final STATE fstState = state.getFst();
			List<ProductState> sndElem = mResStateMap.get(fstState);

			if (sndElem == null) {
				sndElem = new ArrayList<>();
			}
			final List<ProductState> copy = new ArrayList<>();
			// avoid to add pairs are covered by other pairs
			for (int i = 0; i < sndElem.size(); i++) {
				final ProductState elem = sndElem.get(i);
				// pairs covered by the new pair
				// will not be kept in copy
				if (elem.coveredBy(state)) {
					continue;
				}
				if (state.coveredBy(elem)) {
					return false;
				}
				copy.add(elem);
			}

			copy.add(state); // should add snd
			mResStateMap.put(fstState, copy);
			return true;
		}

		public boolean covers(final ProductState state) {
			final List<ProductState> sndElem = mResStateMap.get(state.getFst());
			if (sndElem == null) {
				return false;
			}
			for (int i = 0; i < sndElem.size(); i++) {
				final ProductState elem = sndElem.get(i);
				if (state.coveredBy(elem)) { // no need to add it
					return true;
				}
			}
			return false;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			for (final Entry<STATE, List<ProductState>> entry : mResStateMap.entrySet()) {
				sb.append(entry.getKey() + " -> " + entry.getValue() + "\n");
			}
			return sb.toString();
		}
	}

}
