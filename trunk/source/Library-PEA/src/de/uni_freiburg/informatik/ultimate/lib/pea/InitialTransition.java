package de.uni_freiburg.informatik.ultimate.lib.pea;

public class InitialTransition<T> {
	private final Phase<T> mDest;
	private T mGuard;

	public InitialTransition(final T guard, final Phase<T> dest) {
		mGuard = guard;
		mDest = dest;
	}

	@Override
	public String toString() {
		String destName = mDest.toString();
		if (destName.length() < 33) {
			destName = (destName + "                                 ").substring(0, 33);
		}
		final StringBuffer result = new StringBuffer(" -> ").append(destName).append(" guard ").append(mGuard);

		return result.toString();
	}

	public Phase<T> getDest() {
		return mDest;
	}

	public T getGuard() {
		return mGuard;
	}

	public void setGuard(final T guard) {
		mGuard = guard;
	}
}
