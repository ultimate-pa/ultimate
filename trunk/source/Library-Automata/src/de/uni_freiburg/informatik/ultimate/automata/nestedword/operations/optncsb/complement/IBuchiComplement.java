package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;


import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

public interface IBuchiComplement extends IBuchi {
	IBuchi getOperand();
	void useOpTransition(int letter, IntSet states);
	int getNumUsedOpTransition();
}
