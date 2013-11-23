package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

/**
 * Interface for outgoing (resp. incoming) transitions of nested word automata. 
 * For reasons of efficiency these transitions do not contain the predecessor
 * (resp. successor) because the automaton already stores this information.
 * 
 * The only common object of all these is the letter.
 *
 * @param <LETTER>
 * @param <STATE>
 */
public interface Transitionlet<LETTER,STATE> {
	
	public LETTER getLetter();

}
