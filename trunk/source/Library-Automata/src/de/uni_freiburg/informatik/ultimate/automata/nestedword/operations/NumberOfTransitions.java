/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Operation that returns the number of transitions of a finite automaton.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NumberOfTransitions<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final int mResult;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public NumberOfTransitions(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services);
		mOperand = operand;
		mResult = computeNumberOfTransitions(operand);
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Integer getResult() {
		return mResult;
	}

	private int computeNumberOfTransitions(final INestedWordAutomaton<LETTER, STATE> operand) {
		int number = 0;
		for (final STATE state : operand.getStates()) {
			for (final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator =
					operand.internalSuccessors(state).iterator(); iterator.hasNext();) {
				iterator.next();
				number++;
			}
			for (final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator =
					operand.callSuccessors(state).iterator(); iterator.hasNext();) {
				iterator.next();
				number++;
			}
			for (final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
					operand.returnSuccessors(state).iterator(); iterator.hasNext();) {
				iterator.next();
				number++;
			}
		}
		return number;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
