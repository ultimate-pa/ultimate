/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.logging
 * File:	UltimateLoggers.java created on Feb 23, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.logging;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.FileAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.apache.log4j.spi.LoggerRepository;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

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
	private static UltimateLoggerFactory sInstance;

	private UltimatePreferenceStore mPreferenceStore;
	private List<String> presentLoggers;
	private FileAppender logFile;

	public static final String LOGGER_NAME_CORE = "ultimate";
	public static final String LOGGER_NAME_CONTROLLER = "controller";
	public static final String LOGGER_NAME_PLUGINS = "plugins";
	public static final String LOGGER_NAME_TOOLS = "tools";

	private UltimateLoggerFactory() {

		mPreferenceStore = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);

		initializeLog4J();
		refreshPropertiesLoggerHierarchie();
		refreshPropertiesAppendLogFile();

		// FIXME: Care! Check which properties are relevant for logging and
		// exactly when we have to reload
		// we do not care what property changes, we just reload the logging
		// stuff every time
		mPreferenceStore
				.addPreferenceChangeListener(new IPreferenceChangeListener() {
					@Override
					public void preferenceChange(PreferenceChangeEvent event) {
						refreshPropertiesLoggerHierarchie();
						refreshPropertiesAppendLogFile();
					}
				});
	}

	/**
	 * void initializeLog4J
	 */
	private void initializeLog4J() {

		try {
			// defining format of logging output
			PatternLayout layout = new PatternLayout(
					de.uni_freiburg.informatik.ultimate.plugins.Constants
							.getLoggerPattern());

			// attaching output to console (stout)
			ConsoleAppender consoleAppender = new ConsoleAppender(layout);
			Logger.getRootLogger().addAppender(consoleAppender);

		} catch (Exception ex) {
			System.err.println("Error while initializing logger: " + ex);
			ex.printStackTrace();
		}

	}

	private void refreshPropertiesAppendLogFile() {
		// if log-file should be used, it will be appended here

		if (mPreferenceStore
				.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE)) {
			// if there is already a log file, we remove it!
			if (logFile != null) {
				Logger.getRootLogger().removeAppender(logFile);
				logFile = null;
			}
			String logName = mPreferenceStore
					.getString(CorePreferenceInitializer.LABEL_LOGFILE_NAME);
			String logDir = mPreferenceStore
					.getString(CorePreferenceInitializer.LABEL_LOGFILE_DIR);

			try {
				PatternLayout layout = new PatternLayout(
						de.uni_freiburg.informatik.ultimate.plugins.Constants
								.getLoggerPattern());
				boolean append = mPreferenceStore
						.getBoolean(CorePreferenceInitializer.LABEL_APPEXLOGFILE);
				logFile = new FileAppender(layout, logDir + File.separator
						+ logName + ".log", append);
				Logger.getRootLogger().addAppender(logFile);
			} catch (IOException e) {
				System.err.println("Error while appending log file to logger: "
						+ e);
				e.printStackTrace();
			}
		} else {
			if (logFile != null) {
				Logger.getRootLogger().removeAppender(logFile);
				logFile = null;
			}
		}

	}

	/**
	 * UltimateLoggerFactory getInstance getter for the singleton. lazily
	 * creates the object
	 * 
	 * @return the singleton instance of the UltimateLoggerFactory
	 */
	public static UltimateLoggerFactory getInstance() {
		// lazily initialize the factory
		if (sInstance == null) {
			sInstance = new UltimateLoggerFactory();
		}
		return sInstance;
	}

	/**
	 * Logger getLoggerById
	 * 
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this id.
	 */
	public Logger getLoggerById(String id) {
		return lookupLoggerInHierarchie(id);
	}

	/**
	 * boolean isExternalTool
	 * 
	 * @param id
	 *            Internal logger id.
	 * @return <code>true</code> if and only if this id denotes an external
	 *         tool.
	 */
	private boolean isExternalTool(String id) {
		return id.startsWith(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX);
	}

	/**
	 * Logger lookupLoggerInHierarchie
	 * 
	 * @param id
	 *            Internal logger id.
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

	private void refreshPropertiesLoggerHierarchie() {
		presentLoggers = new LinkedList<String>();
		Logger rootLogger = Logger.getRootLogger();
		rootLogger.setLevel(Level.toLevel(mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_ROOT)));

		// now create children of the rootLogger

		// plug-ins
		LoggerRepository rootRepos = rootLogger.getLoggerRepository();
		Logger pluginsLogger = rootRepos.getLogger(LOGGER_NAME_PLUGINS);
		presentLoggers.add(LOGGER_NAME_PLUGINS);
		String pluginslevel = mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_PLUGINS);
		if (!pluginslevel.isEmpty())
			pluginsLogger.setLevel(Level.toLevel(pluginslevel));

		// external tools
		Logger toolslog = rootRepos.getLogger(LOGGER_NAME_TOOLS);
		presentLoggers.add(LOGGER_NAME_TOOLS);
		String toolslevel = mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_TOOLS);
		if (!toolslevel.isEmpty())
			toolslog.setLevel(Level.toLevel(toolslevel));

		// controller
		Logger controllogger = rootRepos.getLogger(LOGGER_NAME_CONTROLLER);
		String controllevel = mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_CONTROLLER);
		if (!controllevel.isEmpty())
			controllogger.setLevel(Level.toLevel(controllevel));
		presentLoggers.add(LOGGER_NAME_CONTROLLER);

		// core
		Logger corelogger = rootRepos.getLogger(Activator.s_PLUGIN_ID);
		String corelevel = mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_CORE);
		if (!corelevel.isEmpty())
			corelogger.setLevel(Level.toLevel(corelevel));
		presentLoggers.add(Activator.s_PLUGIN_ID);

		// create children for plug-ins
		LoggerRepository piRepos = pluginsLogger.getLoggerRepository();
		String[] plugins = getAllKeys();

		for (String plugin : plugins) {
			Logger logger = piRepos.getLogger(LOGGER_NAME_PLUGINS + "."
					+ plugin);
			logger.setLevel(Level.toLevel(getLogLevel(plugin)));
			presentLoggers.add(logger.getName());
		}

		// create child loggers for external tools
		LoggerRepository toolRepos = toolslog.getLoggerRepository();
		String[] tools = getAllKeys();
		for (String tool : tools) {
			Logger logger = toolRepos.getLogger(LOGGER_NAME_TOOLS + "." + tool);
			logger.setLevel(Level.toLevel(getLogLevel(tool)));
			presentLoggers.add(logger.getName());
		}
	}

	/**
	 * String getLogLevel gets a log level for a certain plug-in
	 * 
	 * @param id
	 *            the id of the plug in
	 * @return the log level or null if no log-level is directly associated
	 */
	private String getLogLevel(String id) {
		String[] pref = getLoggingDetailsPreference();
		for (String string : pref) {
			if (string.startsWith(id + "=")) {
				return string.substring(string.lastIndexOf("=") + 1);
			}
		}
		return null;
	}

	private String[] getLoggingDetailsPreference() {
		return convert(mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_DETAILS));
	}

	private String[] getAllKeys() {
		String[] pref = convert(mPreferenceStore
				.getString(CorePreferenceInitializer.PREFID_DETAILS));
		String[] retVal = new String[pref.length];
		for (int i = 0; i < retVal.length; i++) {
			retVal[i] = pref[i].substring(0, pref[i].lastIndexOf("="));
		}
		return retVal;
	}

	private String[] convert(String preferenceValue) {
		StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
				CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		int tokenCount = tokenizer.countTokens();
		String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}
}
