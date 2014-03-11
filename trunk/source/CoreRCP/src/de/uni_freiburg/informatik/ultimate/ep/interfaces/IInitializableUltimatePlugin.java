package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;

/**
 * 
 * This interface describes IUltimatePlugins that will be initialized by the
 * core.
 * 
 * @author dietsch
 * 
 */
public interface IInitializableUltimatePlugin extends IUltimatePlugin {
	/**
	 * {@link UltimateCore} will call this method according to the
	 * UltimatePlugin livecycle (usually once after the plugin has been loaded
	 * and once before it is used in a toolchain).
	 */
	int init();
}
