/*
 * Copyright (C) 2015 Björn Buchhold
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.logging
 * File:	UltimateLoggers.java created on Feb 23, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.io.File;
import java.io.IOException;
import java.io.Writer;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringTokenizer;

import org.apache.log4j.Appender;
import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.FileAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.apache.log4j.WriterAppender;
import org.apache.log4j.spi.LoggerRepository;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.LogfileException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;

/**
 * UltimateLoggers
 *
 * @author Björn Buchhold
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class Log4JLoggingService implements IStorable, ILoggingService {

	private static final String[] RELEVANT_SETTINGS = new String[] { CorePreferenceInitializer.LABEL_LOG4J_PATTERN,
			CorePreferenceInitializer.LABEL_LOGFILE, CorePreferenceInitializer.LABEL_LOGFILE_NAME,
			CorePreferenceInitializer.LABEL_LOGFILE_DIR, CorePreferenceInitializer.LABEL_APPEXLOGFILE,
			CorePreferenceInitializer.LABEL_LOGLEVEL_ROOT, CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGINS,
			CorePreferenceInitializer.LABEL_LOGLEVEL_TOOLS, CorePreferenceInitializer.LABEL_LOGLEVEL_CONTROLLER,
			CorePreferenceInitializer.LABEL_LOGLEVEL_CORE, CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC,
			CorePreferenceInitializer.LABEL_ROOT_PREF, CorePreferenceInitializer.LABEL_TOOLS_PREF,
			CorePreferenceInitializer.LABEL_CORE_PREF, CorePreferenceInitializer.LABEL_CONTROLLER_PREF,
			CorePreferenceInitializer.LABEL_PLUGINS_PREF, CorePreferenceInitializer.LABEL_PLUGIN_DETAIL_PREF,
			CorePreferenceInitializer.LABEL_COLOR_DEBUG, CorePreferenceInitializer.LABEL_COLOR_INFO,
			CorePreferenceInitializer.LABEL_COLOR_WARNING, CorePreferenceInitializer.LABEL_COLOR_ERROR,
			CorePreferenceInitializer.LABEL_COLOR_FATAL, CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN };

	private static final String APPENDER_NAME_CONSOLE = "ConsoleAppender";
	private static final String APPENDER_NAME_LOGFILE = "LogfileAppender";
	private static final String APPENDER_NAME_CONTROLLER = "ControllerAppender";
	private static final String LOGGER_NAME_CONTROLLER = "controller";

	private static final String LOGGER_NAME_NONCONTROLLER = "noncontroller";

	private static final String LOGGER_NAME_CORE = LOGGER_NAME_NONCONTROLLER + '.' + Activator.PLUGIN_ID;
	private static final String LOGGER_NAME_TOOLS = LOGGER_NAME_NONCONTROLLER + ".tools";
	private static final String LOGGER_NAME_PLUGINS = LOGGER_NAME_NONCONTROLLER + ".plugins";

	/**
	 * Used to distinguish between loggers that were created using {@link #getLogger(String)} and using
	 * {@link #getLoggerForExternalTool(String)}.
	 */
	private static final String LOGGER_NAME_PREFIX_TOOLS = "external.";

	private static final String STORE_KEY = "LoggingService";

	private final RcpPreferenceProvider mPreferenceStore;
	private final IPreferenceChangeListener mRefreshingListener;
	private final Set<Appender> mRootAppenders;
	private final Set<Appender> mControllerAppenders;

	private String mCurrentControllerName;

	private boolean mIsAttached;

	private Map<String, Level> mSettingsLogger2LogLevel;

	private Log4JLoggingService() {
		mPreferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mRootAppenders = new HashSet<>();
		mControllerAppenders = new HashSet<>();

		resetLoggerLevels();
		reinitializeDefaultAppenders();
		reattachAppenders();

		mRefreshingListener = new RefreshingPreferenceChangeListener();
		mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
		mIsAttached = true;
	}

	@Override
	public void reloadLoggers() {
		resetLoggerLevels();
		reinitializeDefaultAppenders();
		reattachAppenders();
		getLogger(Activator.PLUGIN_ID).debug("Logger refreshed");
	}

	private void reinitializeDefaultAppenders() {
		mRootAppenders.clear();
		mControllerAppenders.clear();

		final PatternLayout mainLayout =
				new PatternLayout(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN));
		final Appender consoleAppender = new ConsoleAppender(mainLayout);
		consoleAppender.setName(APPENDER_NAME_CONSOLE);
		mRootAppenders.add(consoleAppender);

		final PatternLayout controllerLayout =
				new PatternLayout(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN));
		final Appender controllerAppender = new ConsoleAppender(controllerLayout);
		controllerAppender.setName(APPENDER_NAME_CONTROLLER);
		mControllerAppenders.add(controllerAppender);

		if (mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE)) {
			final String logName = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_NAME);
			final String logDir = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_DIR);
			final String logFilePattern = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN);
			final boolean append = mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_APPEXLOGFILE);
			final String absolutePath = logDir + File.separator + logName + ".log";
			final PatternLayout logFileLayout = new PatternLayout(logFilePattern);

			try {
				final FileAppender appender = new FileAppender(logFileLayout, absolutePath, append);
				appender.setName(APPENDER_NAME_LOGFILE);
				mRootAppenders.add(appender);
				mControllerAppenders.add(appender);
			} catch (final IOException e) {
				throw new LogfileException(e);
			}
		}
	}

	private void reattachAppenders() {
		reattachAppenders(Logger.getLogger(Log4JLoggingService.LOGGER_NAME_NONCONTROLLER), mRootAppenders);
		reattachAppenders(Logger.getLogger(LOGGER_NAME_CONTROLLER), mControllerAppenders);
	}

	private static void reattachAppenders(final Logger logger, final Collection<Appender> appenders) {
		for (final Appender appender : appenders) {
			logger.removeAppender(appender.getName());
			logger.addAppender(appender);
		}
	}

	private void resetLoggerLevels() {
		// root logger has no name and thus has to be set manually
		final Logger rootLogger = getLog4JRootLogger();
		final Level rootLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_ROOT_PREF);
		rootLogger.setLevel(rootLevel);

		// create all children of the rootLogger; if they have a defined log level, set it to that, else set it to null
		// to remove any manually set log level
		mSettingsLogger2LogLevel = getSettingsLogger2Level();
		final LoggerRepository repo = rootLogger.getLoggerRepository();
		for (final Entry<String, Level> entry : mSettingsLogger2LogLevel.entrySet()) {
			repo.getLogger(entry.getKey()).setLevel(entry.getValue());
		}
	}

	/**
	 * @return
	 * @return A map from logger name to logger level as defined by the current settings
	 */
	private Map<String, Level> getSettingsLogger2Level() {
		final Map<String, Level> rtr = new HashMap<>();
		rtr.put(LOGGER_NAME_CONTROLLER, getLogLevelPreference(CorePreferenceInitializer.LABEL_CONTROLLER_PREF));
		rtr.put(LOGGER_NAME_NONCONTROLLER, getLogLevelPreference(CorePreferenceInitializer.LABEL_ROOT_PREF));
		rtr.put(LOGGER_NAME_PLUGINS, getLogLevelPreference(CorePreferenceInitializer.LABEL_PLUGINS_PREF));
		rtr.put(LOGGER_NAME_TOOLS, getLogLevelPreference(CorePreferenceInitializer.LABEL_TOOLS_PREF));
		rtr.put(LOGGER_NAME_CORE, getLogLevelPreference(CorePreferenceInitializer.LABEL_CORE_PREF));
		// settings for specific plugins
		final Map<String, Level> pluginLevels =
				getSettingPluginSpecificLogLevels(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC);
		for (final Entry<String, Level> entry : pluginLevels.entrySet()) {
			rtr.put(getPluginLoggerName(entry.getKey()), entry.getValue());
		}

		// settings for specific tools
		final Map<String, Level> toolLevels =
				getSettingPluginSpecificLogLevels(CorePreferenceInitializer.LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC);
		for (final Entry<String, Level> entry : toolLevels.entrySet()) {
			rtr.put(getToolLoggerName(entry.getKey()), entry.getValue());
		}
		return rtr;
	}

	private Level getLogLevelPreference(final String label) {
		return Level.toLevel(mPreferenceStore.getString(label));
	}

	/**
	 * boolean isExternalTool
	 *
	 * @param id
	 *            Internal logger id.
	 * @return <code>true</code> if and only if this id denotes an external tool.
	 */
	private static boolean isExternalTool(final String id) {
		return id.startsWith(LOGGER_NAME_PREFIX_TOOLS);
	}

	/**
	 * This function tries to retrieve the correct logger with its associated log-levels based on its id.
	 *
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this internal id.
	 */
	private Logger lookupLoggerInHierarchy(final String id) {
		final String actualLoggerName = getActualLoggerName(id);
		final Logger logger = Logger.getLogger(actualLoggerName);
		final Level logLevel = mSettingsLogger2LogLevel.get(actualLoggerName);
		// may set to null to delete previously set level
		logger.setLevel(logLevel);
		return logger;
	}

	private String getActualLoggerName(final String id) {
		if (id.equals(Activator.PLUGIN_ID)) {
			return LOGGER_NAME_CORE;
		}

		assert mCurrentControllerName != null : "There is no controller";
		if (id.equals(mCurrentControllerName) || id.equals(LOGGER_NAME_CONTROLLER)) {
			return LOGGER_NAME_CONTROLLER;
		}

		if (isExternalTool(id)) {
			return getToolLoggerName(id);
		}
		return getPluginLoggerName(id);
	}

	/**
	 * Returns the full name of a tool logger given the tools name.
	 */
	private static String getToolLoggerName(final String toolId) {
		return LOGGER_NAME_TOOLS + '.' + LOGGER_NAME_PREFIX_TOOLS + toolId;
	}

	/**
	 * Returns the full name of a plugin logger given the plugin name.
	 */
	private static String getPluginLoggerName(final String plugin) {
		return LOGGER_NAME_PLUGINS + "." + plugin;
	}

	@Override
	public void setCurrentControllerID(final String name) {
		mCurrentControllerName = name;
	}

	@Override
	public void destroy() {
		mPreferenceStore.removePreferenceChangeListener(mRefreshingListener);
		mIsAttached = false;
	}

	@Override
	public ILogger getLogger(final String pluginId) {
		return wrapLogger(lookupLoggerInHierarchy(pluginId));
	}

	@Override
	public ILogger getLogger(final Class<?> clazz) {
		return getLogger(clazz.getName());
	}

	@Override
	public ILogger getLoggerForExternalTool(final String id) {
		return getLogger(LOGGER_NAME_PREFIX_TOOLS + id);
	}

	@Override
	public ILogger getControllerLogger() {
		return getLogger(LOGGER_NAME_CONTROLLER);
	}

	private static Logger getLog4JRootLogger() {
		return Logger.getRootLogger();
	}

	@Override
	public void addWriter(final Writer writer, final String logPattern) {
		final Appender appender = new Log4JAppenderWrapper(writer, logPattern);
		if (!mRootAppenders.add(appender)) {
			// it is already added and the pattern cannot be changed without creating a new writer (removing closes the
			// writer)
			return;
		}
		getLog4JRootLogger().addAppender(appender);
	}

	@Override
	public void removeWriter(final Writer writer) {
		final Appender appender = new Log4JAppenderWrapper(writer, null);
		mRootAppenders.remove(appender);
		getLog4JRootLogger().removeAppender(appender);
	}

	private Map<String, Level> getSettingPluginSpecificLogLevels(final String settingsLabel) {
		final String pluginSpecificLogLevels = mPreferenceStore.getString(settingsLabel);
		final StringTokenizer tokenizer =
				new StringTokenizer(pluginSpecificLogLevels, CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);

		final Map<String, Level> rtr = new HashMap<>();
		while (tokenizer.hasMoreTokens()) {
			final String token = tokenizer.nextToken();
			final String[] keyValue = token.split("=");
			rtr.put(keyValue[0], Level.toLevel(keyValue[1]));
		}

		return rtr;
	}

	private static ILogger wrapLogger(final Logger logger) {
		return new Log4JWrapper(logger);
	}

	@Override
	public Object getBacking(final ILogger logger, final Class<?> backingType) {
		if (logger == null || backingType == null) {
			return null;
		}
		if (Logger.class.isAssignableFrom(backingType) && logger instanceof Log4JWrapper) {
			final Log4JWrapper wrappedLogger = (Log4JWrapper) logger;
			return wrappedLogger.getBacking();
		}
		return null;
	}

	static Log4JLoggingService getService(final IToolchainStorage storage) {
		assert storage != null;
		IStorable rtr = storage.getStorable(STORE_KEY);
		if (rtr == null) {
			rtr = new Log4JLoggingService();
			storage.putStorable(STORE_KEY, rtr);
		}
		return (Log4JLoggingService) rtr;
	}

	@Override
	public void store(final IToolchainStorage storage) {
		storage.putStorable(STORE_KEY, this);
		if (!mIsAttached) {
			mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
			reloadLoggers();
		}
	}

	@Override
	public void setLogLevel(final Class<?> clazz, final LogLevel level) {
		setLogLevel(clazz.getName(), level);
	}

	@Override
	public void setLogLevel(final String id, final LogLevel level) {
		mSettingsLogger2LogLevel.put(getPluginLoggerName(id), Level.toLevel(level.toString()));
	}

	private final class RefreshingPreferenceChangeListener implements IPreferenceChangeListener {

		@Override
		public void preferenceChange(final PreferenceChangeEvent event) {
			// do things if it concerns the loggers
			final Object newValue = event.getNewValue();
			final Object oldValue = event.getOldValue();

			if (newValue == null && oldValue == null) {
				return;
			}

			if (newValue != null && newValue.equals(oldValue)) {
				return;
			}

			final String ek = event.getKey();
			if (!Arrays.stream(RELEVANT_SETTINGS).anyMatch(ek::equals)) {
				// it does not concern us, just break
				return;
			}

			// this is an event for which we should refresh the logging service
			reloadLoggers();
		}
	}

	private static final class Log4JAppenderWrapper extends WriterAppender {

		private final Writer mWriter;

		private Log4JAppenderWrapper(final Writer writer, final String pattern) {
			super();
			mWriter = writer;
			setWriter(writer);
			if (pattern != null) {
				setLayout(new PatternLayout(pattern));
			}
			setImmediateFlush(true);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (mWriter == null ? 0 : mWriter.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final Log4JAppenderWrapper other = (Log4JAppenderWrapper) obj;
			if (mWriter == null) {
				if (other.mWriter != null) {
					return false;
				}
			} else if (!mWriter.equals(other.mWriter)) {
				return false;
			}
			return true;
		}
	}

}
