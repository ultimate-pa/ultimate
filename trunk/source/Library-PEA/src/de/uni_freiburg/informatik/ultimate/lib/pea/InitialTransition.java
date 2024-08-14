package de.uni_freiburg.informatik.ultimate.lib.pea;

public class InitialTransition {
	private final Phase mDest;
	private CDD mGuard;

	public InitialTransition(final CDD guard, final Phase dest) {
		mGuard = guard;
		mDest = dest;
	}

	public Phase getDest() {
		return mDest;
	}

	public CDD getGuard() {
		return mGuard;
	}

	public void setGuard(final CDD guard) {
		mGuard = guard;
	}

	@Override
	public String toString() {
		String destName = mDest.toString();
		if (destName.length() < 33) {
			destName = (destName + "                                 ").substring(0, 33);
		}
		final StringBuilder result = new StringBuilder(" -> ").append(destName).append(" guard ").append(mGuard);
		return result.toString();
	}
}
