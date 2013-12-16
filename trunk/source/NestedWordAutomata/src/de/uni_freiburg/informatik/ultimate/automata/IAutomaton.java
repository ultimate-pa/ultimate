package de.uni_freiburg.informatik.ultimate.automata;


import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * All automata have to implement this interface. 
 *
 * @param <LETTER> Type of objects that are contained in the alphabet.
 * @param <STATE> Type of objects that are used to label states (resp. places
 * for PetriNet)
 */
public interface IAutomaton<LETTER,STATE> {
	

	/**
	 * Alphabet of this automaton. 
	 */
	public Set<LETTER> getAlphabet();
	
	/**
	 * StateFactory that was used to construct this automaton. This method 
	 * become deprecated.
	 */
	public StateFactory<STATE> getStateFactory();


	/**
	 * Size of the automaton. E.g., the number of states.
	 */
	public int size();
	
	/**
	 * Provide some human readable information about the size of the automaton. 
	 */
	public String sizeInformation();
}
