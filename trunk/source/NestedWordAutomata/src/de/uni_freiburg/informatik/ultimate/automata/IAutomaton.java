package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public interface IAutomaton<S,C> {
	
	public IRun<S,C> acceptingRun() throws OperationCanceledException;
	public boolean accepts(Word<S> word);
	public int size();
	public Collection<S> getAlphabet();
	public StateFactory<C> getStateFactory();

	
	/**
	 * Provide some human readable information about the size of the automaton. 
	 */
	public String sizeInformation();
}
