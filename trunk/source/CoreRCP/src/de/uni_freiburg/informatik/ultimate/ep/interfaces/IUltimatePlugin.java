package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;

//TODO: Review comments and fix if appropriate 

/**
 * 
 * 
 * @author dietsch
 */
public interface IUltimatePlugin {
	/**
	 * if any kind of initialisation should go here method is called by core
	 * after the plugin is loaded
	 */
	int init(Object params);

	/**
	 * 
	 * @return a human readable Name for the plugin.
	 */
	String getName();

	/**
	 * Returns an unique name for a plugin (unique in the Ultimate eco-system). The canonical choice here is the
	 * package name of the implementer.
	 * 
	 * @return A unique string to identify the plugin. 
	 */
	String getPluginID();

	/**
	 * Is used by preference-changing {@link IController controllers} to
	 * enumerate all available preferences of {@link # IUltimatePlugins} in
	 * order to provide interfaces for users.
	 * 
	 * @return If a plugin uses preferences, it should return its preference
	 *         initializer here. If not, it should return null.
	 */
	UltimatePreferenceInitializer getPreferences();
}
