package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.SccComputation.IStronglyConnectedComponentFactory;


public class SCComponentForNWARSFactory<LETTER, STATE> implements IStronglyConnectedComponentFactory<StateContainer<LETTER, STATE>, SCComponentForNWARS<LETTER, STATE>> {
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_NestedWordAutomatonReachableStates;
	
	

	public SCComponentForNWARSFactory(
			NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates) {
		super();
		m_NestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
	}



	@Override
	public SCComponentForNWARS<LETTER, STATE> constructNewSCComponent() {
		return new SCComponentForNWARS<LETTER, STATE>(m_NestedWordAutomatonReachableStates);
	}
	

}
