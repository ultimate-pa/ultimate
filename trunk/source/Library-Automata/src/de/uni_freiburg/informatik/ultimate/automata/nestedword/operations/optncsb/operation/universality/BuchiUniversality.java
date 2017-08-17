package operation.universality;


import automata.IBuchi;
import complement.BuchiComplementSDBA;

public abstract class BuchiUniversality implements IBuchiUniversality {
	
	protected IBuchi mBuchi;
	protected BuchiComplementSDBA mBuchiComplement;
	
	public BuchiUniversality(IBuchi buchi) {
		this.mBuchi = buchi;
		this.mBuchiComplement = new BuchiComplementSDBA(buchi);
	}

	@Override
	public IBuchi getBuchi() {
		// TODO Auto-generated method stub
		return mBuchi;
	}

	@Override
	public IBuchi getBuchiComplement() {
		// TODO Auto-generated method stub
		return mBuchiComplement;
	}

}
