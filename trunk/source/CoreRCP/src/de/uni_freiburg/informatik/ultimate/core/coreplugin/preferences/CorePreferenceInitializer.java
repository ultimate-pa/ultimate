package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;


import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;


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
public class CorePreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		
	}


// this didn't do anything!	
//	/**
//	 * Initialize default preferences.
//	 */
//	//@Override
//	public void initializeDefaultPreferences() {
//		//obtain the defaultscope
//		IEclipsePreferences defaults = new DefaultScope()
//		.getNode(Activator.s_PLUGIN_ID);
//		//just for demonstration we initialize here with the empty string
//		defaults.putBoolean(IPreferenceConstants.s_NAME_SHOWUSABLEPARSER, IPreferenceConstants.s_VALUE_SHOWUSABLEPARSER_DEFAULT);
//	}

}
