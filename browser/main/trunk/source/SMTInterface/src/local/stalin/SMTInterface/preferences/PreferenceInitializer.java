package local.stalin.SMTInterface.preferences;

import local.stalin.SMTInterface.Activator;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

/**
 * an  example how to do a preference initalizer for your plugin
 * 
 * this class loads preference default values before they are needed
 * 
 * contributes to ep:
 * org.eclipse.core.runtime.preferences.initializer
 * see the plugin.xml
 * 
 * @author Christian Ortolf
 *
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	//@Override
	public void initializeDefaultPreferences() {
		//obtain the defaultscope
		IEclipsePreferences defaults = new DefaultScope()
		.getNode(Activator.PLUGIN_ID);
		
		
		//just for demonstration we initialize here with the empty string
		defaults.put(PreferenceValues.NAME_SMTEXECUTABLE,
				PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT);
		defaults.put(PreferenceValues.NAME_SMTPARAMETER,
				PreferenceValues.VALUE_SMTPARAMETER_DEFAULT);
		defaults.put(PreferenceValues.NAME_TEMPPATH,
				PreferenceValues.VALUE_TEMPPATH_DEFAULT);
		defaults.put(PreferenceValues.NAME_CUSTOMPARMS,
				PreferenceValues.VALUE_CUSTOMPARMS_DEFAULT);
		defaults.putBoolean(PreferenceValues.NAME_SAVESMTLIBFILES,
				PreferenceValues.VALUE_SAVESMTLIBFILES);
	}

}
