package automata;

import java.util.Set;

import util.IntSet;

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
