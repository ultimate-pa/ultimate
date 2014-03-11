package de.uni_freiburg.informatik.ultimate.modelcheckerutils;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;

public final class ModelCheckerUtils implements IUltimatePlugin {

	public static final String sPluginID = "ModelCheckerUtils";
	
	@Override
	public String getName() {
		return sPluginID;
	}

	@Override
	public String getPluginID() {
		return sPluginID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

}
