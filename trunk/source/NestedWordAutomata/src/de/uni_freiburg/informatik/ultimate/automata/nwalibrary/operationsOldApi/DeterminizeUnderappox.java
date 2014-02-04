/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;


/**
 * Determinization where a DeterminizedState is only accepting if all its
 * states are accepting. The language of the resulting automaton is a subset
 * of the language of the original automaton. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class DeterminizeUnderappox<LETTER,STATE> extends DeterminizeDD<LETTER, STATE> {

	public DeterminizeUnderappox(INestedWordAutomatonOldApi<LETTER,STATE> input,
			IStateDeterminizer<LETTER,STATE> stateDeterminizer)
			throws OperationCanceledException {
		super(input, stateDeterminizer);
		}
	
	@Override
	public String operationName() {
		return "determinizeUnderapprox";
	}
	
	/**
	 * Opposed to Determinize, here a Determinized
	 * state is only accepting if all its states are accepting.
	 */
	@Override
	protected Collection<STATE> getInitialStates() {
		ArrayList<STATE> resInitials = 
			new ArrayList<STATE>(m_Operand.getInitialStates().size());
		DeterminizedState<LETTER,STATE> detState = stateDeterminizer.initialState();
		STATE resState = detState.getContent(contentFactory);
		((NestedWordAutomaton<LETTER,STATE>) m_TraversedNwa).addState(true, detState.allFinal(m_Operand), resState);
		det2res.put(detState,resState);
		res2det.put(resState, detState);
		resInitials.add(resState);

		return resInitials;
	}
	
	
	
	/**
	 * Get the state in the resulting automaton that represents a 
	 * DeterminizedState. If this state in the resulting automaton does not
	 * exist yet, construct it. Opposed to Determinize, here a Determinized
	 * state is only accepting if all its states are accepting.
	 */
	@Override
	protected STATE getResState(DeterminizedState<LETTER,STATE> detState) {
		if (det2res.containsKey(detState)) {
			return det2res.get(detState);
		}
		else {
			STATE resState = detState.getContent(contentFactory);
			((NestedWordAutomaton<LETTER,STATE>) m_TraversedNwa).addState(false, detState.allFinal(m_Operand), resState);
			det2res.put(detState,resState);
			res2det.put(resState,detState);
			return resState;
		}
	}
	
	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_TraversedNwa;
	}

}
