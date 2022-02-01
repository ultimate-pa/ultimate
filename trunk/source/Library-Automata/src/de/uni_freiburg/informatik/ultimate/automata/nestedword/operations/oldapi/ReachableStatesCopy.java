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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Wrapper of a nested word automaton where reachability information is stored.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class ReachableStatesCopy<LETTER, STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	private final Map<STATE, STATE> mOld2new = new HashMap<>();
	private final Map<STATE, STATE> mNew2old = new HashMap<>();

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final boolean mComplement;

	/**
	 * Short constructor which does not use the additional options.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 * @see #ReachableStatesCopy(AutomataLibraryServices, INwaOutgoingLetterAndTransitionProvider, boolean, boolean, boolean,
	 *      boolean)
	 */
	public ReachableStatesCopy(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, operand, false, false, false, false);
	}

	/**
	 * Given an {@link INwaOutgoingLetterAndTransitionProvider} return an {@link INestedWordAutomaton} that has the same states, but
	 * all states that are not reachable are omitted. Each state of the result also occurred in the input. Only the
	 * auxiliary empty stack state of the result is different.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param totalize
	 *            {@code true} iff automaton should be totalized
	 * @param complement
	 *            {@code true} iff automaton should be complemented
	 * @param removeDeadEnds
	 *            {@code true} iff dead ends should be removed
	 * @param removeNonLiveStates
	 *            {@code true} iff non-live states should be removed
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public ReachableStatesCopy(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final boolean totalize, final boolean complement,
			final boolean removeDeadEnds, final boolean removeNonLiveStates) throws AutomataOperationCanceledException {
		super(services);
		if (complement && !totalize) {
			throw new IllegalArgumentException("complement requires totalize");
		}
		mComplement = complement;
		mOperand = operand;
		mLogger.info(startMessage());
		mTraversedNwa = new DoubleDeckerAutomaton<>(mServices, operand.getVpAlphabet(), (IEmptyStackStateFactory<STATE>) operand.getStateFactory());
		super.mRemoveDeadEnds = removeDeadEnds;
		super.mRemoveNonLiveStates = removeNonLiveStates;
		final boolean operandHasInitialStates = mOperand.getInitialStates().iterator().hasNext();
		STATE sinkState = null;
		if (totalize || !operandHasInitialStates) {
			sinkState = addSinkState();
		}
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER, STATE>) super.mTraversedNwa).setUp2Down(getUp2DownMapping());
		if (totalize) {
			makeAutomatonTotal(sinkState);
		}
		mLogger.info(exitMessage());
		// assert (new DownStateConsistencyCheck<LETTER, STATE>(mServices,
		// 		(IDoubleDeckerAutomaton) mTraversedNwa)).getResult() : "down states inconsistent";
	}

	private void makeAutomatonTotal(final STATE sinkState) throws AutomataOperationCanceledException {
		assert sinkState != null : "sink state must not be null";
		for (final STATE state : mTraversedNwa.getStates()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			for (final LETTER letter : mTraversedNwa.getVpAlphabet().getInternalAlphabet()) {
				if (!mTraversedNwa.internalSuccessors(state, letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(state, letter,
							sinkState);
				}
			}
			for (final LETTER letter : mTraversedNwa.getVpAlphabet().getCallAlphabet()) {
				if (!mTraversedNwa.callSuccessors(state, letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(state, letter, sinkState);
				}
			}
			makeAutomatonTotalReturn(sinkState, state);
		}
	}

	private void makeAutomatonTotalReturn(final STATE sinkState, final STATE state) {
		for (final LETTER symbol : mTraversedNwa.getVpAlphabet().getReturnAlphabet()) {
			for (final STATE hier : mTraversedNwa.getStates()) {
				if (!mTraversedNwa.returnSuccessors(state, hier, symbol).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(state, hier, symbol,
							sinkState);
				}
			}
		}
	}

	private STATE addSinkState() {
		// TODO Christian 2017-02-15 Cast is a temporary workaround, where do we get a sink state factory here?
		final STATE sinkState = ((ISinkStateFactory<STATE>) mTraversedNwa.getStateFactory()).createSinkStateContent();
		final boolean isInitial = !mOperand.getInitialStates().iterator().hasNext();
		final boolean isFinal = mComplement;
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isFinal, sinkState);
		return sinkState;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Operand " + mOperand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mTraversedNwa.sizeInformation();
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		final Collection<STATE> newInitialStates = new ArrayList<>();
		for (final STATE oldUpState : mOperand.getInitialStates()) {
			final STATE newState = constructOrGetResState(oldUpState, true);
			newInitialStates.add(newState);
		}
		return newInitialStates;
	}

	private STATE constructOrGetResState(final STATE oldUp, final boolean isInitial) {
		if (mOld2new.containsKey(oldUp)) {
			return mOld2new.get(oldUp);
		}
		STATE newState = mOld2new.get(oldUp);
		if (newState == null) {
			newState = oldUp;
			final boolean isAccepting = mOperand.isFinal(oldUp) ^ mComplement;
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isAccepting, newState);
			mOld2new.put(oldUp, newState);
			mNew2old.put(newState, oldUp);
		}
		return newState;

	}

	@Override
	protected Collection<STATE> buildInternalSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<>();
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mNew2old.get(newUpState);
		for (final LETTER symbol : mOperand.lettersInternal(oldUpState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(oldUpState,
					symbol)) {
				final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	@SuppressWarnings("squid:S1698")
	protected Collection<STATE> buildReturnSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<>();
		final STATE newDownState = doubleDecker.getDown();
		// equality intended here
		if (newDownState == mTraversedNwa.getEmptyStackState()) {
			return succs;
		}
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mNew2old.get(newUpState);
		final STATE oldDownState = mNew2old.get(newDownState);

		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(oldUpState,
				oldDownState)) {
			final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(newUpState, newDownState,
					trans.getLetter(), newSucc);
			succs.add(newSucc);
		}
		return succs;
	}

	@Override
	protected Collection<STATE> buildCallSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<>();
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mNew2old.get(newUpState);
		for (final LETTER symbol : mOperand.lettersCall(oldUpState)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(oldUpState, symbol)) {
				final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		return (IDoubleDeckerAutomaton<LETTER, STATE>) mTraversedNwa;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean correct = true;
		if (!mRemoveNonLiveStates) {
			mLogger.info("Start testing correctness of " + getOperationName());
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> input;
			if (!mComplement) {
				input = mOperand;
			} else {
				// intersection of operand and result should be empty
				final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> intersectionOperandResult =
						(new IntersectDD<>(mServices, stateFactory, mOperand, mTraversedNwa)).getResult();
				correct &= (new IsEmpty<>(mServices, intersectionOperandResult)).getResult();
				final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultSadd =
						(new ComplementDD<>(mServices, stateFactory, mOperand)).getResult();
				input = resultSadd;
			}
			// should recognize same language as old computation
			correct &= new IsEquivalent<>(mServices, stateFactory, input, mTraversedNwa).getResult();
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mTraversedNwa);
		}
		return correct;
	}
}
