package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Set;

public interface IDoubleDeckerAutomaton<LETTER, STATE> extends INestedWordAutomatonSimple<LETTER,STATE> {

	public boolean isDoubleDecker(STATE up, STATE down);
	
	public Set<STATE> getDownStates(STATE up);
}
