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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Checks whether a nested word automaton is deterministic.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class IsDeterministic<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final boolean mResult;
	private final boolean mNondeterministicTransitions;
	private final boolean mNondeterministicInitials;

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
	public IsDeterministic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		if (operand instanceof IDoubleDeckerAutomaton) {
			mOperand = (IDoubleDeckerAutomaton<LETTER, STATE>) operand;
		} else {
			mOperand = new NestedWordAutomatonReachableStates<>(mServices, operand);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		mNondeterministicInitials = (mOperand.getInitialStates().size() > 1);
		mNondeterministicTransitions = checkIfOperandhasNondeterministicTransitions();
		mResult = !mNondeterministicInitials && !mNondeterministicTransitions;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private boolean checkIfOperandhasNondeterministicTransitions() {
		for (final STATE upState : mOperand.getStates()) {
			for (final STATE downState : mOperand.getDownStates(upState)) {
				final boolean isNondeterministic = NestedWordAutomataUtils.isNondeterministic(upState, downState, mOperand);
				if (isNondeterministic) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * @return {@code true} iff the automaton has nondeterministic transitions.
	 */
	public boolean hasNondeterministicTransitions() {
		return mNondeterministicTransitions;
	}

	/**
	 * @return {@code true} iff the automaton has more than one initial state.
	 */
	public boolean hasNondeterministicInitials() {
		return mNondeterministicInitials;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Operand is " + (mResult ? "" : "not ") + "deterministic.";
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
