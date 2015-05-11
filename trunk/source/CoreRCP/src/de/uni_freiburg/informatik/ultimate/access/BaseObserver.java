package de.uni_freiburg.informatik.ultimate.access;

import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * Simple construct to implement {@link IUnmanagedObserver}s and ignore extended
 * options. Assumes that the observer does not change the model (i.e.
 * {@link IUnmanagedObserver#performedChanges() returns false}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class BaseObserver implements IUnmanagedObserver {

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {

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
