/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.StateDeterminizerCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceSadd;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.SenwaWalker.ISuccessorVisitor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISenwaStateFactory;

/**
 * Difference operation for {@link Senwa}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class DifferenceSenwa<LETTER, STATE>
		extends BinaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>>
		implements ISuccessorVisitor<LETTER, STATE>, IOpWithDelayedDeadEndRemoval<LETTER, STATE> {
	// TODO Christian 2016-09-18: Can be made INestedWordAutomatonSimple when guarding assertions.
	private final INestedWordAutomaton<LETTER, STATE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSubtrahend;

	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;

	private final ISenwaStateFactory<STATE> mContentFactorySenwa;
	private final IIntersectionStateFactory<STATE> mContentFactoryIntersection;

	private final Senwa<LETTER, STATE> mSenwa;

	private final SenwaWalker<LETTER, STATE> mSenwaWalker;

	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it was created.
	 */
	private final Map<STATE, DifferenceState<LETTER, STATE>> mResult2Operand = new HashMap<>();

	/**
	 * Maps a DifferenceState and an entry state to its representative in the resulting automaton.
	 */
	private final Map<DifferenceState<LETTER, STATE>, Map<DifferenceState<LETTER, STATE>, STATE>> mEntry2Operand2Result =
			new HashMap<>();

	/**
	 * Constructor which uses a {@link PowersetDeterminizer}.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param minuend
	 *            minuend
	 * @param subtrahend
	 *            subtrahend
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public <SF extends ISenwaStateFactory<STATE> & IDeterminizeStateFactory<STATE> & IIntersectionStateFactory<STATE>> DifferenceSenwa(
			final AutomataLibraryServices services, final SF stateFactory,
			final INestedWordAutomaton<LETTER, STATE> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> subtrahend) throws AutomataOperationCanceledException {
		this(services, stateFactory, minuend, subtrahend, new PowersetDeterminizer<>(subtrahend, true, stateFactory),
				true);
	}

	/**
	 * Extended constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param minuend
	 *            minuend
	 * @param subtrahend
	 *            subtrahend
	 * @param stateDeterminizer
	 *            state determinizer
	 * @param removeDeadEndsImmediately
	 *            true iff dead ends should be removed immediately
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public <SF extends ISenwaStateFactory<STATE> & IIntersectionStateFactory<STATE>> DifferenceSenwa(
			final AutomataLibraryServices services, final SF stateFactory,
			final INestedWordAutomaton<LETTER, STATE> minuend,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> subtrahend,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final boolean removeDeadEndsImmediately)
			throws AutomataOperationCanceledException {
		super(services);
		mContentFactorySenwa = stateFactory;
		mContentFactoryIntersection = stateFactory;

		mMinuend = minuend;
		mSubtrahend = subtrahend;
		mLogger.info(startMessage());

		mStateDeterminizer = new StateDeterminizerCache<>(stateDeterminizer);

		mSenwa = new Senwa<>(mServices, minuend.getVpAlphabet(), stateFactory);
		mSenwaWalker = new SenwaWalker<>(mServices, mSenwa, this, removeDeadEndsImmediately);
		mLogger.info(exitMessage());
	}

	private STATE getOrConstructResultState(final DifferenceState<LETTER, STATE> diffEntry,
			final DifferenceState<LETTER, STATE> diffState, final boolean isInitial) {
		assert mMinuend.getStates().contains(diffState.getMinuendState());
		assert mMinuend.getStates().contains(diffEntry.getMinuendState());
		Map<DifferenceState<LETTER, STATE>, STATE> op2res = mEntry2Operand2Result.get(diffEntry);
		if (op2res == null) {
			op2res = new HashMap<>();
			mEntry2Operand2Result.put(diffEntry, op2res);
		}
		STATE resState = op2res.get(diffState);
		if (resState == null) {
			resState = mContentFactorySenwa.senwa(diffEntry.getState(mContentFactoryIntersection, mStateDeterminizer),
					diffState.getState(mContentFactoryIntersection, mStateDeterminizer));
			op2res.put(diffState, resState);
			mResult2Operand.put(resState, diffState);
			final STATE resEntry = op2res.get(diffEntry);
			assert resEntry != null;
			mSenwa.addState(resState, isInitial, diffState.isFinal(), resEntry);
		}
		return resState;
	}

	private DifferenceState<LETTER, STATE> getOperandState(final STATE resState) {
		assert mSenwa.getStates().contains(resState);
		final DifferenceState<LETTER, STATE> opState = mResult2Operand.get(resState);
		assert opState != null;
		return opState;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		final ArrayList<STATE> resInitials = new ArrayList<>();
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		for (final STATE minuState : mMinuend.getInitialStates()) {
			final boolean isFinal = mMinuend.isFinal(minuState) && !detState.containsFinal();
			final DifferenceState<LETTER, STATE> diffState = new DifferenceState<>(minuState, detState, isFinal);
			final STATE resState = getOrConstructResultState(diffState, diffState, true);
			resInitials.add(resState);
		}
		return resInitials;
	}

	@Override
	public Iterable<STATE> visitAndGetInternalSuccessors(final STATE resState) {
		final STATE resEntry = mSenwa.getEntry(resState);
		final DifferenceState<LETTER, STATE> diffEntry = getOperandState(resEntry);
		final Set<STATE> resSuccs = new HashSet<>();
		final DifferenceState<LETTER, STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> subtrState = diffState.getSubtrahendDeterminizedState();
		for (final LETTER letter : mMinuend.lettersInternal(minuState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mMinuend.internalSuccessors(minuState,
					letter)) {
				final STATE minuSucc = trans.getSucc();
				final DeterminizedState<LETTER, STATE> subtrSucc =
						mStateDeterminizer.internalSuccessor(subtrState, letter);
				final boolean isFinal = mMinuend.isFinal(minuSucc) && !subtrSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc = new DifferenceState<>(minuSucc, subtrSucc, isFinal);

				final STATE resSucc = getOrConstructResultState(diffEntry, diffSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addInternalTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetCallSuccessors(final STATE resState) {
		final Set<STATE> resSuccs = new HashSet<>();
		final DifferenceState<LETTER, STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> subtrState = diffState.getSubtrahendDeterminizedState();
		for (final LETTER letter : mMinuend.lettersCall(minuState)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mMinuend.callSuccessors(minuState, letter)) {
				final STATE minuSucc = trans.getSucc();
				final DeterminizedState<LETTER, STATE> subtrSucc = mStateDeterminizer.callSuccessor(subtrState, letter);
				final boolean isFinal = mMinuend.isFinal(minuSucc) && !subtrSucc.containsFinal();
				final DifferenceState<LETTER, STATE> diffSucc = new DifferenceState<>(minuSucc, subtrSucc, isFinal);
				final STATE resSucc = getOrConstructResultState(diffSucc, diffSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addCallTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetReturnSuccessors(final STATE resState, final STATE resHier) {
		final Set<STATE> resSuccs = new HashSet<>();
		final DifferenceState<LETTER, STATE> diffState = getOperandState(resState);
		final STATE minuState = diffState.getMinuendState();
		final DeterminizedState<LETTER, STATE> subtrState = diffState.getSubtrahendDeterminizedState();
		final DifferenceState<LETTER, STATE> diffHier = getOperandState(resHier);
		final STATE minuHier = diffHier.getMinuendState();
		final DeterminizedState<LETTER, STATE> subtrHier = diffHier.getSubtrahendDeterminizedState();
		final STATE resHierEntry = mSenwa.getEntry(resHier);
		final DifferenceState<LETTER, STATE> diffHierEntry = getOperandState(resHierEntry);

		for (final OutgoingReturnTransition<LETTER, STATE> trans : mMinuend.returnSuccessorsGivenHier(minuState, minuHier)) {
			final STATE minuSucc = trans.getSucc();
			final DeterminizedState<LETTER, STATE> subtrSucc =
					mStateDeterminizer.returnSuccessor(subtrState, subtrHier, trans.getLetter());
			final boolean isFinal = mMinuend.isFinal(minuSucc) && !subtrSucc.containsFinal();
			final DifferenceState<LETTER, STATE> diffSucc = new DifferenceState<>(minuSucc, subtrSucc, isFinal);
			final STATE resSucc = getOrConstructResultState(diffHierEntry, diffSucc, false);
			resSuccs.add(resSucc);
			mSenwa.addReturnTransition(resState, resHier, trans.getLetter(), resSucc);
		}
		return resSuccs;
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
	public Senwa<LETTER, STATE> getResult() {
		return mSenwa;
	}

	/**
	 * FIXME: Remove this.
	 *
	 * @param computeRemovedDoubleDeckersAndCallSuccessors
	 *            nocomment
	 * @return nocomment
	 */
	public boolean removeStatesThatCanNotReachFinal(final boolean computeRemovedDoubleDeckersAndCallSuccessors) {
		return mSenwaWalker.removeStatesThatCanNotReachFinal(computeRemovedDoubleDeckersAndCallSuccessors);
	}

	@Override
	public long getDeadEndRemovalTime() {
		return mSenwaWalker.getDeadEndRemovalTime();
	}

	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean removeDeadEnds() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Minuend " + mMinuend.sizeInformation() + ". Subtrahend "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mSenwa.sizeInformation()
				+ ". Max degree of Nondeterminism is " + mStateDeterminizer.getMaxDegreeOfNondeterminism();
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Start testing correctness of " + getOperationName());

			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultSadd =
					(new DifferenceSadd<>(mServices, stateFactory, mMinuend, mSubtrahend)).getResult();
			correct &= new IsEquivalent<>(mServices, stateFactory, resultSadd, mSenwa).getResult();
			if (!correct) {
				AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
						"language is different", mMinuend, mSubtrahend);
			}
			mLogger.info("Finished testing correctness of " + getOperationName());
		} else {
			mLogger.warn("Unable to test correctness if state determinzier is not the PowersetDeterminizer.");
		}
		return correct;
	}
}
