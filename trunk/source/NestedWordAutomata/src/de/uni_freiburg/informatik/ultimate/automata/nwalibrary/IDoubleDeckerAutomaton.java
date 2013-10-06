package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

public interface IDoubleDeckerAutomaton<LETTER, STATE> extends INestedWordAutomatonSimple<LETTER,STATE> {

	public boolean isDoubleDecker(STATE up, STATE down);
}
