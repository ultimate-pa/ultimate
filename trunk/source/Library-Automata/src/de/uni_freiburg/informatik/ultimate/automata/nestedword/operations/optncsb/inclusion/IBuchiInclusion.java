package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.IBuchiComplement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IPair;

public interface IBuchiInclusion {
	
	IBuchi getFstBuchi();
	IBuchi getSndBuchi();
	IBuchiComplement getSndBuchiComplement();
	IBuchi getBuchiDifference();
	
	Boolean isIncluded();
	
    IPair<List<Integer>, List<Integer>> getCounterexampleWord();
    IPair<List<IState>, List<IState>> getCounterexampleRun();
    
    String getName();

}
