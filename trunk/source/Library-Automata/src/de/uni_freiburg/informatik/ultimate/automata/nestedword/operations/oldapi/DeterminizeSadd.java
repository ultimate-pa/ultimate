/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;

/**
 * Determinimization.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class DeterminizeSadd<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final Map<Macrostate, STATE> mMacrostate2detState = new HashMap<>();
	private final Map<STATE, Macrostate> mDetState2macrostate = new HashMap<>();
	private final Map<STATE, Set<STATE>> mSummary = new HashMap<>();
	private final STATE mAuxiliaryEmptyStackState;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	private final IDeterminizeStateFactory<STATE> mStateFactory;

	private final List<StatePair> mQueue = new LinkedList<>();

	// set of pairs that has been visited. The first state of the pair can be any automaton
	// state, the second state is a state that has an outgoing call transition.
	private final Map<STATE, Set<STATE>> mVisited = new HashMap<>();

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public DeterminizeSadd(final AutomataLibraryServices services, final IDeterminizeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mStateFactory = stateFactory;
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = new NestedWordAutomaton<>(mServices, mOperand.getVpAlphabet(), stateFactory);
		mAuxiliaryEmptyStackState = mOperand.getEmptyStackState();
		determinize();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	/**
	 * @param state
	 *            A state.
	 * @param callerState
	 *            a caller state
	 * @return {@code true} iff the caller state was visited
	 */
	public boolean wasVisited(final STATE state, final STATE callerState) {
		final Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			return false;
		}
		return callerStates.contains(callerState);
	}

	/**
	 * @param state
	 *            A state.
	 * @param callerState
	 *            a caller state
	 */
	public void markVisited(final STATE state, final STATE callerState) {
		Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<>();
			mVisited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}

	/**
	 * @param summaryPred
	 *            Summary predecessor.
	 * @param summarySucc
	 *            summary successor
	 */
	public void addSummary(final STATE summaryPred, final STATE summarySucc) {
		Set<STATE> summarySuccessors = mSummary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashSet<>();
			mSummary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.add(summarySucc);
	}

	/**
	 * @param state
	 *            A state.
	 * @param callerState
	 *            a caller state
	 */
	public void enqueueAndMark(final STATE state, final STATE callerState) {
		if (!wasVisited(state, callerState)) {
			markVisited(state, callerState);
			final StatePair statePair = new StatePair(state, callerState);
			mQueue.add(statePair);
		}
	}

	private Set<STATE> getKnownCallerStates(final STATE state) {
		final Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			return new HashSet<>(0);
		}
		return callerStates;
	}

	private void determinize() throws AutomataOperationCanceledException {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Starting determinizeSadd. Operand " + mOperand.sizeInformation());
		}

		final Macrostate initialMacroState = new Macrostate();

		for (final STATE state : mOperand.getInitialStates()) {
			initialMacroState.addPair(state, mAuxiliaryEmptyStackState);
		}
		final STATE initialDetState = initialMacroState.getContent();
		mResult.addState(true, initialMacroState.mIsFinal, initialDetState);
		mMacrostate2detState.put(initialMacroState, initialDetState);
		mDetState2macrostate.put(initialDetState, initialMacroState);
		enqueueAndMark(initialDetState, mAuxiliaryEmptyStackState);

		while (!mQueue.isEmpty()) {
			final StatePair statePair = mQueue.remove(0);
			// mLogger.debug("Processing: "+ statePair);
			processStatePair(statePair);
			if (mSummary.containsKey(statePair.mState)) {
				for (final STATE summarySucc : mSummary.get(statePair.mState)) {
					enqueueAndMark(summarySucc, statePair.mCallerState);
				}

			}
		}
		assert (new IsDeterministic<>(mServices, mResult)).getResult();
	}

	// private void processSummary(IState<LETTER,STATE> summaryPred, IState<LETTER,STATE> summaryPredCaller)

	@SuppressWarnings("squid:S1698")
	private void processStatePair(final StatePair statePair) {
		final STATE detState = statePair.mState;
		final Macrostate macrostate = mDetState2macrostate.get(detState);

		final Set<LETTER> symbolsInternal = new HashSet<>();
		for (final STATE state : macrostate.getStates()) {
			symbolsInternal.addAll(mOperand.lettersInternal(state));
		}
		for (final LETTER symbol : symbolsInternal) {
			final Macrostate succMacrostate = internalSuccMacrostate(macrostate, symbol);
			STATE succDetState = mMacrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				mResult.addState(false, succMacrostate.mIsFinal, succDetState);
				mMacrostate2detState.put(succMacrostate, succDetState);
				mDetState2macrostate.put(succDetState, succMacrostate);
			}
			mResult.addInternalTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, statePair.mCallerState);
		}

		final Set<LETTER> symbolsCall = new HashSet<>();
		for (final STATE state : macrostate.getStates()) {
			symbolsCall.addAll(mOperand.lettersCall(state));
		}
		for (final LETTER symbol : symbolsCall) {
			final Macrostate succMacrostate = callSuccMacrostate(macrostate, symbol);
			STATE succDetState = mMacrostate2detState.get(succMacrostate);
			if (succDetState == null) {
				succDetState = succMacrostate.getContent();
				mResult.addState(false, succMacrostate.mIsFinal, succDetState);
				mMacrostate2detState.put(succMacrostate, succDetState);
				mDetState2macrostate.put(succDetState, succMacrostate);
			}
			mResult.addCallTransition(detState, symbol, succDetState);
			enqueueAndMark(succDetState, detState);
		}

		final STATE detLinPred = statePair.mCallerState;
		// equality intended here
		if (detLinPred != mAuxiliaryEmptyStackState) {

			final Set<LETTER> symbolsReturn = new HashSet<>();
			for (final STATE state : macrostate.getStates()) {
				symbolsReturn.addAll(mOperand.lettersReturn(state));
			}
			for (final LETTER symbol : symbolsReturn) {
				final Macrostate linPredMacrostate = mDetState2macrostate.get(detLinPred);
				final Macrostate succMacrostate = returnSuccMacrostate(macrostate, linPredMacrostate, symbol);
				if (succMacrostate.getStates().isEmpty()) {
					continue;
				}
				STATE succDetState = mMacrostate2detState.get(succMacrostate);
				if (succDetState == null) {
					succDetState = succMacrostate.getContent();
					mResult.addState(false, succMacrostate.mIsFinal, succDetState);
					mMacrostate2detState.put(succMacrostate, succDetState);
					mDetState2macrostate.put(succDetState, succMacrostate);
				}
				mResult.addReturnTransition(detState, detLinPred, symbol, succDetState);
				addSummary(detLinPred, succDetState);
				for (final STATE detLinPredCallerState : getKnownCallerStates(detLinPred)) {
					enqueueAndMark(succDetState, detLinPredCallerState);
				}
			}
		}
	}

	/**
	 * Compute successor Macrostate under internal transition of a Macrostate and symbol.
	 */
	private Macrostate internalSuccMacrostate(final Macrostate macrostate, final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state, symbol)) {
				final STATE succ = trans.getSucc();
				final Set<STATE> callerStates = macrostate.getCallerStates(state);
				succMacrostate.addPairs(succ, callerStates);
			}
		}
		return succMacrostate;
	}

	/**
	 * Compute successor Macrostate under call transition of a Macrostate and symbol.
	 */
	private Macrostate callSuccMacrostate(final Macrostate macrostate, final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state, symbol)) {
				final STATE succ = trans.getSucc();
				succMacrostate.addPair(succ, state);
			}
		}
		return succMacrostate;
	}

	/**
	 * Compute successor Macrostate under return transition of a Macrostate, a linear predecessor Macrostate and a
	 * symbol.
	 */
	private Macrostate returnSuccMacrostate(final Macrostate macrostate, final Macrostate linPredMacrostate,
			final LETTER symbol) {
		final Macrostate succMacrostate = new Macrostate();
		for (final STATE state : macrostate.getStates()) {
			for (final STATE linPred : macrostate.getCallerStates(state)) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(state, linPred,
						symbol)) {
					returnSuccMacrostateHelper(linPredMacrostate, succMacrostate, linPred, trans);
				}
			}
		}
		return succMacrostate;
	}

	private void returnSuccMacrostateHelper(final Macrostate linPredMacrostate, final Macrostate succMacrostate,
			final STATE linPred, final OutgoingReturnTransition<LETTER, STATE> trans) {
		final STATE succ = trans.getSucc();
		final Set<STATE> callerStates = linPredMacrostate.getCallerStates(linPred);
		if (callerStates != null) {
			succMacrostate.addPairs(succ, callerStates);
		}
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of determinization");
		}

		boolean correct;
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultDd =
				(new DeterminizeDD<>(mServices, stateFactory, mOperand)).getResult();
		correct = (new IsEquivalent<>(mServices, stateFactory, resultDd, mResult)).getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of determinization");
		}
		return correct;
	}

	/**
	 * A pair of state and caller state.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class StatePair {
		private final STATE mState;
		private final STATE mCallerState;
		private final int mHashCode;

		public StatePair(final STATE state, final STATE callerState) {
			mState = state;
			mCallerState = callerState;
			mHashCode = computeHashCode();
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null || getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final StatePair other = (StatePair) obj;
			if (!getOuterType().equals(other.getOuterType())) {
				return false;
			}
			if (mCallerState == null) {
				if (other.mCallerState != null) {
					return false;
				}
			} else if (!mCallerState.equals(other.mCallerState)) {
				return false;
			}
			if (mState == null) {
				if (other.mState != null) {
					return false;
				}
			} else if (!mState.equals(other.mState)) {
				return false;
			}
			return true;
		}

		@Override
		public int hashCode() {
			return mHashCode;
		}

		private final int computeHashCode() {
			final int prime = 31;
			int result = prime + getOuterType().hashCode();
			result = prime * result + ((mCallerState == null) ? 0 : mCallerState.hashCode());
			result = prime * result + ((mState == null) ? 0 : mState.hashCode());
			return result;
		}

		@Override
		public String toString() {
			return "CallerState: " + mCallerState + "  State: " + mState;
		}

		private DeterminizeSadd<LETTER, STATE> getOuterType() {
			return DeterminizeSadd.this;
		}
	}

	/**
	 * List of pairs of States.
	 */
	private class Macrostate {
		private final Map<STATE, Set<STATE>> mPairList;
		private boolean mIsFinal;

		public Macrostate() {
			mPairList = new HashMap<>();
			mIsFinal = false;
		}

		Set<STATE> getStates() {
			return mPairList.keySet();
		}

		Set<STATE> getCallerStates(final STATE state) {
			return mPairList.get(state);
		}

		boolean isFinal() {
			return mIsFinal;
		}

		STATE getContent() {
			return mStateFactory.determinize(mPairList);
		}

		private void addPair(final STATE state, final STATE callerState) {
			if (mOperand.isFinal(state)) {
				mIsFinal = true;
			}
			Set<STATE> callerStates = mPairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<>();
				mPairList.put(state, callerStates);
			}
			callerStates.add(callerState);
		}

		private void addPairs(final STATE state, final Set<STATE> newCallerStates) {
			if (mOperand.isFinal(state)) {
				mIsFinal = true;
			}
			Set<STATE> callerStates = mPairList.get(state);
			if (callerStates == null) {
				callerStates = new HashSet<>();
				mPairList.put(state, callerStates);
			}
			callerStates.addAll(newCallerStates);
		}

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (obj == null) {
				return false;
			}
			if (this.getClass() != obj.getClass()) {
				return false;
			}
			final Macrostate macrostate = (Macrostate) obj;
			return mPairList.equals(macrostate.mPairList);
		}

		@Override
		public int hashCode() {
			return mPairList.hashCode();
		}

		@Override
		public String toString() {
			return mPairList.toString();
		}
	}
}
