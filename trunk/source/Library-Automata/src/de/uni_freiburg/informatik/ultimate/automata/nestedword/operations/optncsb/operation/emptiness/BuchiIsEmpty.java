package operation.emptiness;

import java.util.List;

import util.IPair;

public interface BuchiIsEmpty {
	
	Boolean isEmpty();
	
	IPair<List<Integer>, List<Integer>> getAcceptingWord();

}
