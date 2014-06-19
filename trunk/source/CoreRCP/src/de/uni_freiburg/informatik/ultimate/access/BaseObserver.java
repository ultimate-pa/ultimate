package de.uni_freiburg.informatik.ultimate.access;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

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

	protected static Logger sLogger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

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
