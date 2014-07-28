package de.uni_freiburg.informatik.ultimate.core.services;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

public interface ILoggingService {

	/**
	 * Gets the correct logger for an asking plug-in This method should be
	 * called by all plug-ins that extend {@link ITool} and by the Core Plugin
	 * and want to access their {@link Logger}. Appenders are set as defaults
	 * and log levels are set using preferences <br/>
	 * <br/>
	 * <b>Usage:</b> Most tools can use their Activator.s_PLUGIN_ID as argument<br/>
	 * <br/>
	 * Not to be used for external tools or the controller plug-in
	 * 
	 * @param pluginId
	 *            The PluginId of the plug-in that asks for its {@link Logger}
	 * @return the log4j {@link Logger} for the plug-in
	 */
	public abstract Logger getLogger(String pluginId);

	/**
	 * Gets the correct logger for an asking external tool This method should be
	 * called by all external tools that want to access their {@link Logger}.
	 * Appenders are set as defaults and log levels are set using the
	 * preferences <br/>
	 * 
	 * Not to be used for plug-ins!
	 * 
	 * @param id
	 *            An identifier for the external tool that asks for its
	 *            {@link Logger}
	 * @return the log4j {@link Logger} for the external tool
	 */
	public abstract Logger getLoggerForExternalTool(String id);

	/**
	 * Gets the correct logger for the controller plug-in. This method should be
	 * called by all controller plug-ins that want to access their
	 * {@link Logger}. Appenders are set as defaults and log levels are set
	 * using the Eclipse IPreferenceStore <br/>
	 * 
	 * @return Logger for the current controller.
	 */
	public abstract Logger getControllerLogger();

}