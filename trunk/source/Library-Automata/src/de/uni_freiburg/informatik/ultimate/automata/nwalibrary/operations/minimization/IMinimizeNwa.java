package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * General minimization interface.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public interface IMinimizeNwa<LETTER, STATE> {
	/**
	 * @return the resulting automaton 
	 */
	INestedWordAutomaton<LETTER, STATE> getResult();
	
	/**
	 * Run some checks to test correctness of the result.
	 * @param stateFactory state factory
	 * @return true iff all tests succeeded
	 * @throws AutomataLibraryException when tests call failing methods
	 */
	boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException;
}
