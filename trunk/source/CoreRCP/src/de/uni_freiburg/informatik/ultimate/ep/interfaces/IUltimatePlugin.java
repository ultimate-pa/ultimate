package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;

/**
 * An IUltimatePlugin describes the most basic interface for all plugins that
 * together form the Ultimate ecosystem.
 * 
 * The methods at this level are used to provide
 * <ul>
 * <li>Different log levels for different plugins via preferences in the core</li>
 * <li>The ability to define preferences per plugin that can be changed by the
 * user</li>
 * </ul>
 * 
 * 
 * TODO: Currently, preferences are only loaded for implementers of of
 * {@link IController}, {@link ICore} and {@link IToolchainPlugin}! Library
 * plugins that implement this interface directly are out of luck! The current
 * intention is that library plugins do not implement any of the cores
 * interfaces (subject to change)<br>
 * <br>
 * Clients should subclass this interface if they want to define a library
 * plugin. For toolchain plugins (i.e. the regular Ultimate plugins) see
 * {@link IToolchainPlugin}.
 * 
 * @author dietsch
 */
public interface IUltimatePlugin {
	/**
	 * 
	 * @return Returns a human-readable name for the plugin. This will be shown
	 *         in the user interface and in most logs.
	 */
	String getPluginName();

	/**
	 * Returns the name of the package of the implementing class as per the Java
	 * Language Specification. You can get that name for example with
	 * {@code getClass().getPackage().getName()} or, e.g.,
	 * {@code JungVisualization.class.getPackage().getName()}. <br>
	 * <br>
	 * The correct implementation of this interface also requires that
	 * implementers must use the string provided here (case-sensitive) as
	 * <ul>
	 * <li>{@code Bundle-SymbolicName} in the plugin's MANIFEST.MF</li>
	 * <li>{@code <artifactId>} in the plugin's pom.xml</li>
	 * <li>{@code id} in feature.xml files used to include this plugin in build
	 * features (i.e. BA_FeatureUltimate...)</li>
	 * <li>After performing those changes and recompiling, you may have to resync your Launch Configurations</li>
	 * </ul>
	 * 
	 * Implementers of {@link ICore} and {@link IController} have to take
	 * additional steps: TODO: Describe additional steps
	 * 
	 * @return The name of the namespace of the implementing class.
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
