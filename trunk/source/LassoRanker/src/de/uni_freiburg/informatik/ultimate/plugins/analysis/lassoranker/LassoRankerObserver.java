package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class LassoRankerObserver implements IUnmanagedObserver {
	
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	@Override
	public boolean process(IElement root) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		s_Logger.debug("Current Preferences:\n" + Preferences.show());
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
