package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.preferences;


import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;


/**
 * 
 * This class loads preference default values before they are needed
 * 
 * contributes to ep:
 * org.eclipse.core.runtime.preferences.initializer
 * see the plugin.xml
 * 
 * @author dietsch
 *
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	//@Override
	public void initializeDefaultPreferences() {
		//IEclipsePreferences defaults = new DefaultScope().getNode(Activator.PLUGIN_ID);

		//defaults.put(PreferenceValues.NAME_SHOWALLANNOTATIONS,
			//	PreferenceValues.VALUE_SHOWALLANNOTATIONS_DEFAULT);
	}

}
