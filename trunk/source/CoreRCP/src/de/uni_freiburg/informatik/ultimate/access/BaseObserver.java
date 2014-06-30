package de.uni_freiburg.informatik.ultimate.access;


/***
 * 
 * Simple construct to implement {@link IUnmanagedObserver}s and ignore extended
 * options. Assumes that the observer does not change the model (i.e.
 * {@link IUnmanagedObserver#performedChanges() returns false}.
 * 
 * @author dietsch
 * 
 */
public abstract class BaseObserver implements IUnmanagedObserver {

	@Override
	public void init() {

	}

	@Override
	public void finish() {

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
