package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IState;

public interface IStateComplement extends IState {
	
	IBuchi getOperand();
	
	IBuchi getComplement();
}
