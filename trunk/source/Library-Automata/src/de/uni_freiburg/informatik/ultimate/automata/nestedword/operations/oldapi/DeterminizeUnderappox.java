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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Determinization where a DeterminizedState is only accepting if all its states are accepting. The language of the
 * resulting automaton is a subset of the language of the original automaton.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DeterminizeUnderappox<LETTER, STATE> extends DeterminizeDD<LETTER, STATE> {
	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public DeterminizeUnderappox(final AutomataLibraryServices services,
			final IEmptyStackStateFactory<STATE> emptyStackFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataOperationCanceledException {
		super(services, emptyStackFactory, operand, stateDeterminizer);
	}

	/**
	 * As opposed to {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Determinize Determinize},
	 * here a determinized state is only accepting if all its states are accepting.
	 */
	@Override
	protected Collection<STATE> getInitialStates() {
		// final ArrayList<STATE> resInitials = new ArrayList<>(mOperand.getInitialStates().size());
		final ArrayList<STATE> resInitials = new ArrayList<>();
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		final STATE resState = mStateDeterminizer.getState(detState);
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(true, detState.allFinal(mOperand), resState);
		mDet2res.put(detState, resState);
		mRes2det.put(resState, detState);
		resInitials.add(resState);

		return resInitials;
	}

	/**
	 * Get the state in the resulting automaton that represents a DeterminizedState. If this state in the resulting
	 * automaton does not exist yet, construct it. As opposed to
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Determinize Determinize}, here a
	 * determinized state is only accepting if all its states are accepting.
	 */
	@Override
	protected STATE getResState(final DeterminizedState<LETTER, STATE> detState) {
		if (mDet2res.containsKey(detState)) {
			return mDet2res.get(detState);
		}
		final STATE resState = mStateDeterminizer.getState(detState);
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(false, detState.allFinal(mOperand), resState);
		mDet2res.put(detState, resState);
		mRes2det.put(resState, detState);
		return resState;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mTraversedNwa;
	}
}
