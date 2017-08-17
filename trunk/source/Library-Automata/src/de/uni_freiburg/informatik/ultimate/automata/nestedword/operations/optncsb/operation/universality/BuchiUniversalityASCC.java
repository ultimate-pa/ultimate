package operation.universality;

import java.util.List;

import automata.IBuchi;
import operation.emptiness.BuchiIsEmpty;
import operation.emptiness.BuchiIsEmptyASCC;
import util.IPair;

public class BuchiUniversalityASCC extends BuchiUniversality {

	public BuchiUniversalityASCC(IBuchi buchi) {
		super(buchi);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Boolean isUniversal() {
		// TODO Auto-generated method stub
		BuchiIsEmpty checker = new BuchiIsEmptyASCC(mBuchiComplement, 10 * 1000);
		return checker.isEmpty();
	}

	@Override
	public IPair<List<Integer>, List<Integer>> getCounterexampleWord() {
		// TODO Auto-generated method stub
		return null;
	}

}
