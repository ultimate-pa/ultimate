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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Class that computes a handle of an automaton.
 * <p>
 * We call an initial run of an automaton a <i>handle</i> if
 * <ul>
 * <li>there is exactly one initial state
 * <li>each state but the last of the run has exactly one successor
 * <li>each state but the first of the run has exactly one predecessor
 * <li>no state occurs more than once in the handle (automaton does not have
 * a cycle shape)
 * </ul>
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class GetHandle<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private NestedRun<LETTER, STATE> mHandle;
	private final NoHandleReason mNoHandleReason;

	/**
	 * Available reasons why the automaton is no handle.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private enum NoHandleReason {
		/**
		 * Multiple initial states.
		 */
		MULTI_INITIAL,
		/**
		 * Cycle in the automaton.
		 */
		CYCLE_SHAPE,
		/**
		 * Multiple successors of the initial state.
		 */
		MULTI_INIT_SUCC
	}

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public GetHandle(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		if (mOperand.getInitialStates().size() != 1) {
			mNoHandleReason = NoHandleReason.MULTI_INITIAL;
		} else {
			final STATE singleInitial = mOperand.getInitialStates().iterator().next();
			mHandle = getSingleSuccessor(singleInitial);
			if (mHandle == null) {
				mNoHandleReason = NoHandleReason.MULTI_INIT_SUCC;
			} else {
				mNoHandleReason = aa();
			}
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private NoHandleReason aa() {
		while (true) {
			final STATE knownPredecessor = mHandle.getStateAtPosition(mHandle.getLength() - 2);
			final STATE current = mHandle.getStateAtPosition(mHandle.getLength() - 1);
			final boolean singlePred = hasSinglePredecessor(current, knownPredecessor);
			if (!singlePred) {
				return null;
			}
			final NestedRun<LETTER, STATE> newSuffix = getSingleSuccessor(current);
			if (newSuffix == null) {
				return null;
			}
			mHandle = mHandle.concatenate(newSuffix);
			if (mHandle.getLength() > mOperand.size()) {
				if (mLogger.isInfoEnabled()) {
					mLogger.info("automaton has cycle shape");
				}
				mHandle = null;
				return NoHandleReason.CYCLE_SHAPE;
			}
		}
	}

	/**
	 * TODO Christian 2016-09-04: This method is not used elsewhere. Make it private?
	 * 
	 * @param state
	 *            state
	 * @return a run of length 2 from the given state to its successor
	 */
	public NestedRun<LETTER, STATE> getSingleSuccessor(final STATE state) {
		NestedRun<LETTER, STATE> result = null;
		for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mOperand.internalSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<>(state, outTrans.getLetter(), NestedWord.INTERNAL_POSITION, outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (final OutgoingCallTransition<LETTER, STATE> outTrans : mOperand.callSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<>(state, outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mOperand.returnSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<>(state, outTrans.getLetter(), NestedWord.MINUS_INFINITY, outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		return result;
	}

	/**
	 * TODO Christian 2016-09-04: This method is not used elsewhere. Make it private?
	 * 
	 * @param state
	 *            state
	 * @param knownPredecessor
	 *            predecessor state (only used for assertion)
	 * @return {@code true} iff the state has a single predecessor state (namely the one passed)
	 */
	@SuppressWarnings("squid:S1698")
	public boolean hasSinglePredecessor(final STATE state, final STATE knownPredecessor) {
		STATE predecessor = null;
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : mOperand.internalPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		for (final IncomingCallTransition<LETTER, STATE> inTrans : mOperand.callPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		for (final IncomingReturnTransition<LETTER, STATE> inTrans : mOperand.returnPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getLinPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		if (predecessor == null) {
			return false;
		}
		// equality check intended here
		assert predecessor == knownPredecessor : "wrong state";
		return true;
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public NestedRun<LETTER, STATE> getResult() {
		return mHandle;
	}

	@Override
	public String operationName() {
		return "GetHandle";
	}

	@Override
	public String exitMessage() {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append("Finished ")
				.append(operationName());
		// @formatter:on
		if (mHandle == null) {
			// @formatter:off
			builder.append(". Automaton has no handle. Reason: ")
					.append(mNoHandleReason);
			// @formatter:on
		} else {
			// @formatter:off
			builder.append(". Found word of length ")
					.append(mHandle.getLength());
			// @formatter:on
		}
		return builder.toString();
	}
}
