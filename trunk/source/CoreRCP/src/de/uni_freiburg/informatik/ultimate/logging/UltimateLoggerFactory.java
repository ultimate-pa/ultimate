/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.logging
 * File:	UltimateLoggers.java created on Feb 23, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.logging;

import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.IPreferenceConstants;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.LoggingDetailsPreferenceWrapper;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.LoggingToolDetailsPreferenceWrapper;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.apache.log4j.spi.LoggerRepository;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * UltimateLoggers
 * 
 * @author Bj�rn Buchhold
 * 
 */
public class UltimateLoggerFactory {

	/**
	 * the singleton
	 */
	private static UltimateLoggerFactory instance;

	private IPreferenceStore preferenceStore;
	private List<String> presentLoggers;

	public static final String LOGGER_NAME_CORE = "ultimate";
	public static final String LOGGER_NAME_CONTROLLER = "controller";
	public static final String LOGGER_NAME_PLUGINS = "plugins";
	public static final String LOGGER_NAME_TOOLS = "tools";

	private UltimateLoggerFactory() {
		initializeLog4J();
		this.preferenceStore = new ScopedPreferenceStore(new InstanceScope(),
				Activator.s_PLUGIN_ID);
		updateLoggerHierarchie();
	}

	/**
	 * void initializeLog4J
	 */
	private void initializeLog4J() {

		try {
			// defining format of logging output
			PatternLayout layout = new PatternLayout(
					de.uni_freiburg.informatik.ultimate.plugins.Constants.getLoggerPattern());

			// attaching output to console (stout)
			ConsoleAppender consoleAppender = new ConsoleAppender(layout);
			Logger.getRootLogger().addAppender(consoleAppender);

		} catch (Exception ex) {
			System.err.println("Error while initializing logger: " + ex);
			ex.printStackTrace();
		}

	}

	/**
	 * UltimateLoggerFactory getInstance getter for the singleton. lazily creates
	 * the object
	 * 
	 * @return the singleton instance of the UltimateLoggerFactory
	 */
	public static UltimateLoggerFactory getInstance() {
		// lazily initialize the factory
		if (instance == null) {
			instance = new UltimateLoggerFactory();
		}
		return instance;
	}

	/**
	 * Logger getLoggerById
	 * 
	 * @param id Internal logger id.
	 * @return Logger for this id.
	 */
	public Logger getLoggerById(String id) {
		return lookupLoggerInHierarchie(id);
	}

	/**
	 * boolean isExternalTool
	 * 
	 * @param id Internal logger id.
	 * @return <code>true</code> if and only if this id denotes an external
	 * 			tool.
	 */
	private boolean isExternalTool(String id) {
		return id.startsWith(IPreferenceConstants.EXTERNAL_TOOLS_PREFIX);
	}

	/**
	 * Logger lookupLoggerInHierarchie
	 * 
	 * @param id Internal logger id.
	 * @return Logger for this internal id.
	 */
	private Logger lookupLoggerInHierarchie(String id) {
		// it is core
		if (id.equals(Activator.s_PLUGIN_ID)) {
			return Logger.getLogger(LOGGER_NAME_CORE);
		}
		// it is a controller
		if (id.equals(UltimateServices.getInstance().getActiveControllerId())) {
			return Logger.getLogger(LOGGER_NAME_CONTROLLER);
		}
		// it is a declared one for no tool
		if (presentLoggers.contains(LOGGER_NAME_PLUGINS + "." + id)
				&& !isExternalTool(id)) {
			return Logger.getLogger(LOGGER_NAME_PLUGINS + "." + id);
		}
		// it is a declared one for a tool
		if (presentLoggers.contains(LOGGER_NAME_TOOLS + "." + id)
				&& isExternalTool(id)) {
			return Logger.getLogger(LOGGER_NAME_TOOLS + "." + id);
		}
		// it is an external tool with no logger specified
		if (isExternalTool(id)) {
			return Logger.getLogger(LOGGER_NAME_TOOLS);
		}
		// otherwise it has to be some plug-in with no logger specified
		return Logger.getLogger(LOGGER_NAME_PLUGINS);
	}

	/**
	 * void buildLoggerHierarchie
	 */
	public void updateLoggerHierarchie() {
		presentLoggers = new LinkedList<String>();
		Logger rootLogger = Logger.getRootLogger();
		rootLogger.setLevel(Level.toLevel(preferenceStore
				.getString(IPreferenceConstants.PREFID_ROOT)));

		// now create children of the rootLogger

		// plug-ins
		LoggerRepository rootRepos = rootLogger.getLoggerRepository();
		Logger pluginsLogger = rootRepos.getLogger(LOGGER_NAME_PLUGINS);
		presentLoggers.add(LOGGER_NAME_PLUGINS);
		String pluginslevel = preferenceStore.
			getString(IPreferenceConstants.PREFID_PLUGINS);
		if (!pluginslevel.isEmpty())
			pluginsLogger.setLevel(Level.toLevel(pluginslevel));

		// external tools
		Logger toolslog = rootRepos.getLogger(LOGGER_NAME_TOOLS);
		presentLoggers.add(LOGGER_NAME_TOOLS);
		String toolslevel = preferenceStore.
			getString(IPreferenceConstants.PREFID_TOOLS);
		if (!toolslevel.isEmpty())
			toolslog.setLevel(Level.toLevel(toolslevel));

		// controller
		Logger controllogger = rootRepos.getLogger(LOGGER_NAME_CONTROLLER);
		String controllevel = preferenceStore.
			getString(IPreferenceConstants.PREFID_CONTROLLER);
		if (!controllevel.isEmpty())
			controllogger.setLevel(Level.toLevel(controllevel));
		presentLoggers.add(LOGGER_NAME_CONTROLLER);

		// core
		Logger corelogger = rootRepos.getLogger(Activator.s_PLUGIN_ID);
		String corelevel = preferenceStore.
			getString(IPreferenceConstants.PREFID_CORE);
		if (!corelevel.isEmpty())
			corelogger.setLevel(Level.toLevel(corelevel));
		presentLoggers.add(Activator.s_PLUGIN_ID);

		// create children for plug-ins
		LoggerRepository piRepos = pluginsLogger.getLoggerRepository();
		String[] plugins = LoggingDetailsPreferenceWrapper.getAllKeys();

		for (String plugin : plugins) {
			Logger logger = piRepos.getLogger(LOGGER_NAME_PLUGINS + "."
					+ plugin);
			logger.setLevel(Level.toLevel(LoggingDetailsPreferenceWrapper
					.getLogLevel(plugin)));
			presentLoggers.add(logger.getName());
		}

		// create child loggers for external tools
		LoggerRepository toolRepos = toolslog.getLoggerRepository();
		String[] tools = LoggingToolDetailsPreferenceWrapper.getAllKeys();
		for (String tool : tools) {
			Logger logger = toolRepos.getLogger(LOGGER_NAME_TOOLS + "." + tool);
			logger.setLevel(Level.toLevel(LoggingToolDetailsPreferenceWrapper
					.getLogLevel(tool)));
			presentLoggers.add(logger.getName());
		}
	}
}
