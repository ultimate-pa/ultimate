package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

public interface Acc {
	
	boolean isAccepted(IntSet set);
	
	List<IntSet> getAccs();
	
}
