package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.CommandLineParser;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;

/**
 * This interface describes the object that is passed to
 * {@link IController#init(ICore, ILoggingService)}.
 * 
 * {@link IController} should use at least {@link #requestToolchain()} and
 * {@link #releaseToolchain(IToolchain)} to receive {@link IToolchain} instances
 * through which Ultimate is actually controlled.
 * 
 * @author dietsch
 * 
 */
public interface ICore {

	/**
	 * Don't forget to release the toolchain after use.
	 * 
	 * @return An {@link IToolchain} instance that can be initialized and
	 *         started.
	 */
	IToolchain requestToolchain();

	/**
	 * Release a previously requested {@link IToolchain} instance to invalidate
	 * all resources.
	 * 
	 * @param toolchain
	 */
	void releaseToolchain(IToolchain toolchain);

	/**
	 * ICore will try to save all settings different from the default settings
	 * to the given path. An existing file will be overwritten.
	 * 
	 * @return An absolute path to a (possibly existing) .epf file
	 */
	void savePreferences(String absolutePath);

	/**
	 * ICore will try to load new settings from the given path.
	 * 
	 * @return An absolute path to a .epf settings file compatible with
	 *         Ultimate's settings.
	 */
	void loadPreferences(String absolutePath);

	/**
	 * Get an instance of every {@link IUltimatePlugin} that is known to the
	 * Core (this will load every UltimatePlugin).
	 * 
	 * @return
	 */
	IUltimatePlugin[] getRegisteredUltimatePlugins();

	/**
	 * Get the name of every registered {@link IUltimatePlugin}. This will allow
	 * you to prepare for lazy loading of plugins.
	 * 
	 * @return
	 */
	String[] getRegisteredUltimatePluginIDs();

	/**
	 * 
	 * @return
	 */
	CommandLineParser getCommandLineArguments();

}
