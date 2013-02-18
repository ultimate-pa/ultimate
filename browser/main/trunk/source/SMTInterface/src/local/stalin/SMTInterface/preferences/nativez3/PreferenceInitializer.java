package local.stalin.SMTInterface.preferences.nativez3;

import local.stalin.SMTInterface.Activator;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

public class PreferenceInitializer extends AbstractPreferenceInitializer {

	public static final String NATIVEZ3CONFIG = "nativez3config";
	public final static String SEPARATOR = "\n";
	
	@Override
	public void initializeDefaultPreferences() {
		//obtain the defaultscope
		IEclipsePreferences defaults = new DefaultScope()
		.getNode(Activator.PLUGIN_ID);
		defaults.put(NATIVEZ3CONFIG, "");
	}

}
