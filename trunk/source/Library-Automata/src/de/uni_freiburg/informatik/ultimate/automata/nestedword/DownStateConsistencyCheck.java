/*
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Check if down states of an automaton are stored consistently.
 * <p>
 * This operation is only useful for debugging.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DownStateConsistencyCheck<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private static final String DOWN_STATES_INCONSISTENT = "The down states are inconsistent.";

	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final boolean mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public DownStateConsistencyCheck(final AutomataLibraryServices services,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mResult = consistentForAll();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	private boolean consistentForAll() throws AutomataOperationCanceledException {
		boolean result;
		result = consistentForInitials();
		for (final STATE state : mOperand.getStates()) {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			result = result && consistentForState(state);
		}
		return result;
	}

	private boolean consistentForInitials() {
		boolean result = true;
		for (final STATE state : mOperand.getInitialStates()) {
			final Set<STATE> downStates = mOperand.getDownStates(state);
			result = result && downStates.contains(mOperand.getEmptyStackState());
		}
		assert result : DOWN_STATES_INCONSISTENT;
		return result;
	}

	private boolean consistentForState(final STATE state) {
		boolean result;
		final Set<STATE> downStates = mOperand.getDownStates(state);
		result = getIsComparison(state, downStates);
		result = result && checkIfDownStatesArePassedToSuccessors(state, downStates);
		result = result && checkIfEachDownStateIsJustified(state, downStates);
		assert result : DOWN_STATES_INCONSISTENT;
		return result;
	}

	private boolean checkIfEachDownStateIsJustified(final STATE state, final Set<STATE> downStatesIn) {
		final HashSet<STATE> downStates = new HashSet<>(downStatesIn);
		for (final IncomingInternalTransition<LETTER, STATE> t : mOperand.internalPredecessors(state)) {
			final Set<STATE> preDown = mOperand.getDownStates(t.getPred());
			downStates.removeAll(preDown);
		}

		for (final IncomingCallTransition<LETTER, STATE> t : mOperand.callPredecessors(state)) {
			downStates.remove(t.getPred());
		}

		for (final IncomingReturnTransition<LETTER, STATE> t : mOperand.returnPredecessors(state)) {
			final Set<STATE> predDownStates = mOperand.getDownStates(t.getLinPred());
			if (predDownStates.contains(t.getHierPred())) {
				final Set<STATE> hierDownStates = mOperand.getDownStates(t.getHierPred());
				downStates.removeAll(hierDownStates);
			} else {
				throw new AssertionError("unreachable return");
			}
		}
		if (mOperand.isInitial(state)) {
			downStates.remove(mOperand.getEmptyStackState());
		}
		if (!downStates.isEmpty()) {
			mLogger.warn("State " + state + " has unjustified down states " + downStates);
		}
		return downStates.isEmpty();
	}

	private boolean checkIfDownStatesArePassedToSuccessors(final STATE state, final Set<STATE> downStates) {
		boolean result = true;
		for (final OutgoingInternalTransition<LETTER, STATE> t : mOperand.internalSuccessors(state)) {
			final Set<STATE> succDownStates = mOperand.getDownStates(t.getSucc());
			result = result && succDownStates.containsAll(downStates);
			assert result : DOWN_STATES_INCONSISTENT;
		}
		for (final OutgoingCallTransition<LETTER, STATE> t : mOperand.callSuccessors(state)) {
			final Set<STATE> succDownStates = mOperand.getDownStates(t.getSucc());
			result = result && succDownStates.contains(state);
			assert result : DOWN_STATES_INCONSISTENT;
		}
		for (final OutgoingReturnTransition<LETTER, STATE> t : mOperand.returnSuccessors(state)) {
			final Set<STATE> succDownStates = mOperand.getDownStates(t.getSucc());
			final Set<STATE> hierDownStates = mOperand.getDownStates(t.getHierPred());
			if (downStates.contains(t.getHierPred())) {
				result = result && succDownStates.containsAll(hierDownStates);
				assert result : DOWN_STATES_INCONSISTENT;
			} else {
				// nothing to check, we cannot take this transition
			}
		}
		for (final SummaryReturnTransition<LETTER, STATE> t : mOperand.summarySuccessors(state)) {
			final Set<STATE> succDownStates = mOperand.getDownStates(t.getSucc());
			result = result && succDownStates.containsAll(downStates);
			assert result : DOWN_STATES_INCONSISTENT;
		}
		return result;
	}

	/**
	 * Check if {@link IDoubleDeckerAutomaton#getDownStates(Object)} and
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)} are consistent.
	 */
	private boolean getIsComparison(final STATE state, final Set<STATE> downStates) {
		return getIsComparison1(state, downStates) && getIsComparison2(state, downStates);
	}

	/**
	 * Check if doubleDeckers claimed by {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)} are a superset of
	 * the doubleDeckers claimed by {@link IDoubleDeckerAutomaton#getDownStates(Object)}.
	 */
	private boolean getIsComparison1(final STATE state, final Set<STATE> downStates) {
		boolean result = true;
		for (final STATE down : downStates) {
			result = result && mOperand.isDoubleDecker(state, down);
		}
		return result;
	}

	/**
	 * Check if doubleDeckers claimed by {@link IDoubleDeckerAutomaton#getDownStates(Object)} are a superset of the
	 * doubleDeckers claimed by {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)} This check is expensive,
	 * because we have to iterate over all states.
	 */
	private boolean getIsComparison2(final STATE state, final Set<STATE> downStates) {
		boolean result = true;
		for (final STATE down : mOperand.getStates()) {
			if (mOperand.isDoubleDecker(state, down)) {
				result = result && downStates.contains(down);
			}
		}
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// I don't know a useful check
		return true;
	}
}
