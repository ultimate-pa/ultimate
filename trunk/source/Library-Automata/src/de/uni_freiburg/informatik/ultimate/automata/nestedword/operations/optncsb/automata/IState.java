package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

public interface IState {
	
	int getId();
		
	void addSuccessor(int letter, int state);
	
	IntSet getSuccessors(int letter);
	
	Set<Integer> getEnabledLetters();

	// ----- general requirements
	boolean equals(Object otherState);
	
	int hashCode();
	
	String toString();
}
