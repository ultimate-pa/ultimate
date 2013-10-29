package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

/**
 * an example how to do a preference initalizer for your plugin
 * 
 * this class loads preference default values before they are needed
 * 
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the
 * plugin.xml
 * 
 * @author Christian Ortolf
 * 
 */
public class CorePreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		// This method is called by the preference initializer to initialize
		// default preference values. Clients should get the correct node for
		// their bundle and then set the default values on it. For example:
		IEclipsePreferences node = DefaultScope.INSTANCE.getNode(Activator.s_PLUGIN_ID);
//		node.putBoolean("", false);
		
	}
}
