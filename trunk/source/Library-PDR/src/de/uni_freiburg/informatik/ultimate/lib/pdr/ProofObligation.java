package de.uni_freiburg.informatik.ultimate.lib.pdr;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public final class ProofObligation {

	private final IPredicate mToBeBlocked;
	private final IcfgLocation mLocation;
	private final int mLevel;
	private IPredicate mReason;
	private Boolean mHasBeenBlocked;
	
	public ProofObligation(final IPredicate toBeBlocked, final IcfgLocation location, final int level, final IPredicate reason) {
		mToBeBlocked = toBeBlocked;
		mLocation = location;
		mLevel = level;
		mReason = reason;
		mHasBeenBlocked = false;
	}

	public Boolean hasBeenBlocked() {
		return mHasBeenBlocked;
	}
	
	public void setReason(final IPredicate newReason) {
		mReason = newReason;
		mHasBeenBlocked = true;
	}
	
	public IPredicate getToBeBlocked() {
		return mToBeBlocked;
	}
	
	public IcfgLocation getLocation() {
		return mLocation;
	}
	
	public int getLevel() {
		return mLevel;
	}
	
	public IPredicate getReason() {
		return mReason;
	}

}
