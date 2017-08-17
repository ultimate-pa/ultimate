package operation.universality;

import java.util.List;

import automata.IBuchi;
import util.IPair;

// check whether given Buchi accepts \sigma^\omega

public interface IBuchiUniversality {
	
	IBuchi getBuchi();
	IBuchi getBuchiComplement();
	
	Boolean isUniversal();
	
	IPair<List<Integer>, List<Integer>> getCounterexampleWord();

}
