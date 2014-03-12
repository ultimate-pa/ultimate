package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;

/**
 * An IUltimatePlugin describes the most basic interface for all plugins that
 * together form the Ultimate eco-system.
 * 
 * The methods at this level are used to provide
 * <ul>
 * <li>different log levels for different plugins via preferences in the core</li>
 * <li>the ability to define preferences per plugin that can be changed by the user</li>
 * </ul>
 * 
 * Clients should not subclass this interface except if they want to define a Library plugin.
 * For default Ultimate plugins see {@link IToolchainPlugin}.
 * 
 * @author dietsch
 */
public interface IUltimatePlugin {
	/**
	 * 
	 * @return Returns a human-readable name for the plugin. This will be shown
	 *         in user interfaces.
	 */
	String getName();

	/**
	 * Returns an unique name for a plugin (unique in the Ultimate eco-system).
	 * The canonical choice here is the package name of the implementer.
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
