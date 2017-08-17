package operation.inclusion;

import java.util.List;

import automata.IBuchi;
import automata.IState;
import complement.IBuchiComplement;
import util.IPair;

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
