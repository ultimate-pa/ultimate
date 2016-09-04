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
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
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


/**
 * Class that computes a handle of an automaton.
 * We call an initial run of an automaton a <i>handle</i> if
 * <ul>
 * <li> there is exactly one initial state
 * <li> each state but the last of the run has exactly one successor
 * <li> each state but the first of the run has exactly one predecessor
 * <li> no state occurs more than once in the handle (automaton does not have
 * a cycle shape)
 * </ul>
 * @author Matthias Heizmann
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class GetHandle<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER,STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	
	private NestedRun<LETTER,STATE> mHandle;
	private NoHandleReason mNoHandleReason;
	
	private enum NoHandleReason {
		MULTI_INITIAL, CYCLE_SHAPE, MULTI_INIT_SUCC
	}
	
	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	public GetHandle(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		if (mOperand.getInitialStates().size() != 1) {
			mNoHandleReason = NoHandleReason.MULTI_INITIAL;
		} else {
			final STATE singleInitial = mOperand.getInitialStates().iterator().next();
			mHandle = getSingleSuccessor(singleInitial);
			if (mHandle == null) {
				mNoHandleReason = NoHandleReason.MULTI_INIT_SUCC;
			} else {
				while (true) {
					final STATE knownPredecessor = mHandle.getStateAtPosition(mHandle.getLength() - 2);
					final STATE current = mHandle.getStateAtPosition(mHandle.getLength() - 1);
					final boolean singlePred = hasSinglePredecessor(current, knownPredecessor);
					if (!singlePred) {
						break;
					}
					final NestedRun<LETTER, STATE> newSuffix = getSingleSuccessor(current);
					if (newSuffix == null) {
						break;
					} else {
						mHandle = mHandle.concatenate(newSuffix);
					}
					if (mHandle.getLength() > mOperand.size()) {
						mLogger.info("automaton has cycle shape");
						mHandle = null;
						mNoHandleReason = NoHandleReason.CYCLE_SHAPE;
						break;
					}
				}
			}
		}
		mLogger.info(exitMessage());
	}
	
	
	public NestedRun<LETTER,STATE> getSingleSuccessor(final STATE state) {
		NestedRun<LETTER,STATE> result = null;
		for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mOperand.internalSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state,
						outTrans.getLetter(), NestedWord.INTERNAL_POSITION,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (final OutgoingCallTransition<LETTER, STATE> outTrans : mOperand.callSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state,
						outTrans.getLetter(), NestedWord.PLUS_INFINITY,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mOperand.returnSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state,
						outTrans.getLetter(), NestedWord.MINUS_INFINITY,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		return result;
	}
	
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
		} else {
			assert predecessor == knownPredecessor : "wrong state";
			return true;
		}
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public NestedRun<LETTER,STATE> getResult() {
		return mHandle;
	}

	@Override
	public String operationName() {
		return "getHandle";
	}

	@Override
	public String exitMessage() {
		String result = "Finished " + operationName();
		if (mHandle == null) {
			result += ". Automaton has no handle. Reason: " + mNoHandleReason;
		} else {
			result += ". Found word of length " + mHandle.getLength();
		}
		return result;
	}
}
