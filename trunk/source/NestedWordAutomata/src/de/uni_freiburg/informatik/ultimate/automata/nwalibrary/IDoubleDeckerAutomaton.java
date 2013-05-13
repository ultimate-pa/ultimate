package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

public interface IDoubleDeckerAutomaton<LETTER, STATE> {

	public boolean isDoubleDecker(STATE up, STATE down);
}
