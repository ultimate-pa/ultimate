package de.uni_freiburg.informatik.ultimate.irsdependencies.observers;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;

public abstract class BaseObserver implements IUnmanagedObserver {
	
	protected static Logger sLogger = UltimateServices.getInstance()
			.getLogger(Activator.PLUGIN_ID);

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
