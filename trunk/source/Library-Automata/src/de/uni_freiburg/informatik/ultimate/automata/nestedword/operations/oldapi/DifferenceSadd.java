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
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a DifferenceAutomatonBuilder can compute a NWA
 * nwa_difference such that nwa_difference accepts all words that are accepted by nwa_minuend but not by
 * Psi(nwa_subtrahend), i.e. L(nwa_difference) = L(nwa_minuend) \ L( Psi(nwa_subtrahend) ), where Psi is a
 * transformation of the automaton nwa_subtrahend that is defined by an implementation of IStateDeterminizer.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of automata. In many cases you want to use
 *            String as STATE and your states are labeled e.g. with "q0", "q1", ...
 */
public final class DifferenceSadd<LETTER, STATE>
		extends BinaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final INestedWordAutomaton<LETTER, STATE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSubtrahend;
	private final NestedWordAutomaton<LETTER, STATE> mDifference;

	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;

	/**
	 * Maps a DifferenceState to its representative in the resulting automaton.
	 */
	private final Map<DifferenceState, STATE> mDiff2res = new HashMap<>();

	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it was created.
	 */
	private final Map<STATE, DifferenceState> mRes2diff = new HashMap<>();

	/**
	 * Summary states of the resulting automaton that have been visited so far. If the summary state
	 * (<i>caller</i>,<i>present</i>) has been visited, <i>present</i> is contained in the range of <i>caller</i>.
	 */
	private final Map<STATE, Set<STATE>> mVisited = new HashMap<>();

	/**
	 * Summary states of the resulting automaton that still have to be processed.
	 */
	private final List<SummaryState> mWorklist = new LinkedList<>();

	/**
	 * Pairs of states (q,q') of the resulting automaton such that q' is reachable from q via a well-matched nested word
	 * in which the first position is a call position and the last position is a return position.
	 */
	private final Map<STATE, Set<STATE>> mSummary = new HashMap<>();

	private final STATE mAuxiliaryEmptyStackState;

	private final IIntersectionStateFactory<STATE> mContentFactory;

	/**
	 * Constructor where powerset determinizer is used.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param minuend
	 *            minuend
	 * @param subtrahend
	 *            subtrahend
	 * @throws AutomataLibraryException
	 *             if alphabets are different
	 */
	public <SF extends IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>> DifferenceSadd(
			final AutomataLibraryServices services, final SF stateFactory,
			final INestedWordAutomaton<LETTER, STATE> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> subtrahend) throws AutomataLibraryException {
		this(services, stateFactory, minuend, subtrahend, new PowersetDeterminizer<>(subtrahend, true, stateFactory));
	}

	/**
	 * Constructor with a given state determinizer.
	 *
	 * @param services
	 *            Ultimate services
	 * @param contentFactory
	 *            state factory
	 * @param minuend
	 *            minuend
	 * @param subtrahend
	 *            subtrahend
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataLibraryException
	 *             if alphabets differ
	 */
	public DifferenceSadd(final AutomataLibraryServices services, final IIntersectionStateFactory<STATE> contentFactory,
			final INestedWordAutomaton<LETTER, STATE> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> subtrahend,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataLibraryException {
		super(services);

		if (!NestedWordAutomataUtils.sameAlphabet(minuend, subtrahend)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}

		mContentFactory = contentFactory;
		mMinuend = minuend;
		mSubtrahend = subtrahend;
		mStateDeterminizer = stateDeterminizer;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mDifference = new NestedWordAutomaton<>(mServices, minuend.getVpAlphabet(), contentFactory);
		mAuxiliaryEmptyStackState = mDifference.getEmptyStackState();
		computeDifference();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Minuend " + mMinuend.sizeInformation() + ". Subtrahend "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mDifference.sizeInformation();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mMinuend;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSubtrahend;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mDifference;
	}

	/**
	 * @param callerState
	 *            A caller state.
	 * @param state
	 *            a state
	 * @return {@code true} iff caller state was visited
	 */
	public boolean wasVisited(final STATE callerState, final STATE state) {
		final Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			return false;
		}
		return callerStates.contains(callerState);
	}

	/**
	 * @param callerState
	 *            A caller state.
	 * @param state
	 *            a state
	 */
	public void markVisited(final STATE callerState, final STATE state) {
		Set<STATE> callerStates = mVisited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<>();
			mVisited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}

	/**
	 * @param callerState
	 *            A caller state.
	 * @param state
	 *            a state
	 */
	public void enqueueAndMark(final STATE callerState, final STATE state) {
		if (!wasVisited(callerState, state)) {
			markVisited(callerState, state);
			final SummaryState statePair = new SummaryState(state, callerState);
			mWorklist.add(statePair);
		}
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
	 * Get all states <i>resCaller</i> of the resulting automaton (computed so far) such that the summary state
	 * (<i>resCaller</i>,<i>resPresent</i>) has been visited so far.
	 */
	private Set<STATE> getKnownCallerStates(final STATE resPresent) {
		final Set<STATE> callerStates = mVisited.get(resPresent);
		if (callerStates == null) {
			return new HashSet<>(0);
		}
		return callerStates;
	}

	/**
	 * Performs the actual difference computation.
	 */
	public void computeDifference() {
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		for (final STATE minuState : mMinuend.getInitialStates()) {
			final DifferenceState macrState = new DifferenceState(minuState, detState);
			final STATE diffState = mContentFactory.intersection(macrState.mMinuendState,
					mStateDeterminizer.getState(macrState.mSubtrahendDeterminizedState));
			mDifference.addState(true, macrState.isFinal(), diffState);
			mDiff2res.put(macrState, diffState);
			mRes2diff.put(diffState, macrState);
			enqueueAndMark(mAuxiliaryEmptyStackState, diffState);
		}

		while (!mWorklist.isEmpty()) {
			final SummaryState statePair = mWorklist.remove(0);
			// mLogger.debug("Processing: "+ statePair);
			processSummaryState(statePair);
			if (mSummary.containsKey(statePair.mPresentState)) {
				for (final STATE summarySucc : mSummary.get(statePair.mPresentState)) {
					enqueueAndMark(statePair.getCallerState(), summarySucc);
				}
			}
		}
	}

	/**
	 * Let resSummaryState=(<i>caller</i>,<i>present</i>). Extend the construction of the resulting automaton at
	 * <i>present</i> by outgoing transitions. To decide if a return transition can be added <i>caller</i> is taken into
	 * account.
	 */
	@SuppressWarnings("squid:S1698")
	private void processSummaryState(final SummaryState resSummaryState) {
		final STATE resState = resSummaryState.getPresentState();
		final DifferenceState diffState = mRes2diff.get(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> detState = diffState.getSubtrahendDeterminizedState();

		for (final LETTER symbol : mMinuend.lettersInternal(minuState)) {
			if (!mSubtrahend.getVpAlphabet().getInternalAlphabet().contains(symbol)) {
				continue;
			}
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.internalSuccessor(detState, symbol);
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mMinuend.internalSuccessors(minuState,
					symbol)) {
				final STATE minuSucc = trans.getSucc();
				final DifferenceState diffSucc = new DifferenceState(minuSucc, detSucc);
				final STATE resSucc = getResState(diffSucc);
				mDifference.addInternalTransition(resState, symbol, resSucc);
				enqueueAndMark(resSummaryState.getCallerState(), resSucc);
			}
		}

		for (final LETTER symbol : mMinuend.lettersCall(minuState)) {
			if (!mSubtrahend.getVpAlphabet().getCallAlphabet().contains(symbol)) {
				continue;
			}
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.callSuccessor(detState, symbol);
			for (final OutgoingCallTransition<LETTER, STATE> trans : mMinuend.callSuccessors(minuState, symbol)) {
				final STATE minuSucc = trans.getSucc();
				final DifferenceState diffSucc = new DifferenceState(minuSucc, detSucc);
				final STATE resSucc = getResState(diffSucc);
				mDifference.addCallTransition(resState, symbol, resSucc);
				enqueueAndMark(resState, resSucc);
			}
		}

		for (final LETTER symbol : mMinuend.lettersReturn(minuState)) {
			if (!mSubtrahend.getVpAlphabet().getReturnAlphabet().contains(symbol)) {
				continue;
			}
			final STATE resLinPred = resSummaryState.getCallerState();
			// equality intended here
			if (resLinPred == mAuxiliaryEmptyStackState) {
				continue;
			}
			final DifferenceState diffLinPred = mRes2diff.get(resLinPred);
			final STATE minuLinPred = diffLinPred.getMinuendState();
			final DeterminizedState<LETTER, STATE> detLinPred = diffLinPred.getSubtrahendDeterminizedState();

			final Iterable<OutgoingReturnTransition<LETTER, STATE>> minuTransitions =
					mMinuend.returnSuccessors(minuState, minuLinPred, symbol);
			// if (minuSuccs.isEmpty()) continue;
			final DeterminizedState<LETTER, STATE> detSucc =
					mStateDeterminizer.returnSuccessor(detState, detLinPred, symbol);
			for (final OutgoingReturnTransition<LETTER, STATE> trans : minuTransitions) {
				final STATE minuSucc = trans.getSucc();
				final DifferenceState diffSucc = new DifferenceState(minuSucc, detSucc);
				final STATE resSucc = getResState(diffSucc);
				mDifference.addReturnTransition(resState, resLinPred, symbol, resSucc);
				addSummary(resLinPred, resSucc);
				for (final STATE resLinPredCallerState : getKnownCallerStates(resLinPred)) {
					enqueueAndMark(resLinPredCallerState, resSucc);
				}
			}
		}
	}

	/**
	 * Get the state in the resulting automaton that represents a DifferenceState. If this state in the resulting
	 * automaton does not exist yet, construct it.
	 */
	STATE getResState(final DifferenceState diffState) {
		if (mDiff2res.containsKey(diffState)) {
			return mDiff2res.get(diffState);
		}
		final STATE resState = mContentFactory.intersection(diffState.mMinuendState,
				mStateDeterminizer.getState(diffState.mSubtrahendDeterminizedState));
		mDifference.addState(false, diffState.isFinal(), resState);
		mDiff2res.put(diffState, resState);
		mRes2diff.put(resState, diffState);
		return resState;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + getOperationName());

			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultDd =
					(new DifferenceDD<>(mServices, stateFactory, mMinuend, mSubtrahend)).getResult();
			correct = new IsEquivalent<>(mServices, stateFactory, resultDd, mDifference).getResult();
			if (!correct) {
				mLogger.info("Finished testing correctness of " + getOperationName());
			} else {
				mLogger.warn("Unable to test correctness if state determinizer is not the PowersetDeterminizer.");
			}
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mMinuend, mSubtrahend);
		}
		return correct;
	}

	/**
	 * State of an NWA that accepts the language difference of two NWAs. A DifferenceState is a pair whose first entry
	 * is a state of the minuend, the second entry is a DeterminizedState of the subtrahend. A DifferenceState is final
	 * iff the minuend state is final and the subtrahend state is not final.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class DifferenceState {
		private static final int PRIME_1 = 3;
		private static final int PRIME_2 = 5;

		private final STATE mMinuendState;
		private final DeterminizedState<LETTER, STATE> mSubtrahendDeterminizedState;
		private final boolean mIsFinal;
		private final int mHashCode;

		public DifferenceState(final STATE minuendState,
				final DeterminizedState<LETTER, STATE> subtrahendDeterminizedState) {
			mMinuendState = minuendState;
			mSubtrahendDeterminizedState = subtrahendDeterminizedState;
			mIsFinal = mMinuend.isFinal(minuendState) && !subtrahendDeterminizedState.containsFinal();
			mHashCode = PRIME_1 * minuendState.hashCode() + PRIME_2 * subtrahendDeterminizedState.hashCode();
			//FIXME: hashCode of StatePairList may change over time!
		}

		public STATE getMinuendState() {
			return mMinuendState;
		}

		public DeterminizedState<LETTER, STATE> getSubtrahendDeterminizedState() {
			return mSubtrahendDeterminizedState;
		}

		public boolean isFinal() {
			return mIsFinal;
		}

		/**
		 * Two DifferenceStates are equivalent iff each, their minuend states and their subtrahend states are
		 * equivalent.
		 */
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (obj == null || this.getClass() != obj.getClass()) {
				return false;
			}
			final DifferenceState diffState = (DifferenceState) obj;
			return diffState.mMinuendState.equals(mMinuendState)
					&& mSubtrahendDeterminizedState.equals(diffState.mSubtrahendDeterminizedState);
		}

		@Override
		public int hashCode() {
			return mHashCode;
		}

		@Override
		public String toString() {
			return "<[< " + mMinuendState.toString() + " , " + mSubtrahendDeterminizedState.toString() + ">]>";
		}
	}

	/**
	 * A summary state.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class SummaryState {
		private static final int PRIME_1 = 3;
		private static final int PRIME_2 = 5;

		private final STATE mCallerState;
		private final STATE mPresentState;
		private final int mHashCode;

		public SummaryState(final STATE presentState, final STATE callerState) {
			mCallerState = callerState;
			mPresentState = presentState;
			mHashCode = PRIME_1 * callerState.hashCode() + PRIME_2 * presentState.hashCode();
		}

		public STATE getCallerState() {
			return mCallerState;
		}

		public STATE getPresentState() {
			return mPresentState;
		}

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (obj == null || this.getClass() != obj.getClass()) {
				return false;
			}
			final SummaryState summaryState = (SummaryState) obj;
			return mPresentState.equals(summaryState.mPresentState) && mCallerState.equals(summaryState.mCallerState);
		}

		@Override
		public int hashCode() {
			return mHashCode;
		}

		@Override
		public String toString() {
			return "CallerState: " + mCallerState + "  State: " + mPresentState;
		}
	}
}
