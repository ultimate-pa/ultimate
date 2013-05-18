package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;


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

public class DeterminizeUnderappox<LETTER,STATE> extends Determinize<LETTER, STATE> {

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
