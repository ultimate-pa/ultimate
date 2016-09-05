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
import java.util.HashSet;
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
			CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX, CorePreferenceInitializer.PREFID_ROOT,
			CorePreferenceInitializer.PREFID_PLUGINS, CorePreferenceInitializer.PREFID_TOOLS,
			CorePreferenceInitializer.PREFID_CONTROLLER, CorePreferenceInitializer.PREFID_CORE,
			CorePreferenceInitializer.PREFID_DETAILS, CorePreferenceInitializer.LABEL_ROOT_PREF,
			CorePreferenceInitializer.LABEL_TOOLS_PREF, CorePreferenceInitializer.LABEL_CORE_PREF,
			CorePreferenceInitializer.LABEL_CONTROLLER_PREF, CorePreferenceInitializer.LABEL_PLUGINS_PREF,
			CorePreferenceInitializer.LABEL_PLUGIN_DETAIL_PREF, CorePreferenceInitializer.LABEL_COLOR_DEBUG,
			CorePreferenceInitializer.LABEL_COLOR_INFO, CorePreferenceInitializer.LABEL_COLOR_WARNING,
			CorePreferenceInitializer.LABEL_COLOR_ERROR, CorePreferenceInitializer.LABEL_COLOR_FATAL,
			CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN };

	private static final String APPENDER_NAME_CONSOLE = "ConsoleAppender";
	private static final String APPENDER_NAME_LOGFILE = "LogfileAppender";
	private static final String APPENDER_NAME_CONTROLLER = "ControllerAppender";
	private static final String LOGGER_NAME_CONTROLLER = "controller";
	private static final String LOGGER_NAME_PLUGINS = "plugins";
	private static final String LOGGER_NAME_TOOLS = "tools";
	private static final String LOGGER_NAME_NONCONTROLLER = "noncontroller";
	private static final String STORE_KEY = "LoggingService";

	private static int sId;

	private final RcpPreferenceProvider mPreferenceStore;
	private final IPreferenceChangeListener mRefreshingListener;
	private final Set<Appender> mRootAppenders;
	private final Set<Appender> mControllerAppenders;

	private final Set<String> mLiveLoggerIds;
	private String mCurrentControllerName;

	private Log4JLoggingService() {
		mPreferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mRootAppenders = new HashSet<>();
		mControllerAppenders = new HashSet<>();
		mLiveLoggerIds = new HashSet<>();

		recreateLoggerHierarchie();
		reinitializeDefaultAppenders();
		reattachAppenders();

		mRefreshingListener = new RefreshingPreferenceChangeListener();
		mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
		sId++;
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
		reattachAppenders(getNonControllerRootLogger(), mRootAppenders);
		reattachAppenders(getControllerRootLogger(), mControllerAppenders);
	}

	private static void reattachAppenders(final Logger logger, final Collection<Appender> appenders) {
		for (final Appender appender : appenders) {
			logger.removeAppender(appender.getName());
			logger.addAppender(appender);
		}
	}

	private void recreateLoggerHierarchie() {
		mLiveLoggerIds.clear();
		final Logger rootLogger = getLog4JRootLogger();
		final Level rootLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_ROOT_PREF);
		rootLogger.setLevel(rootLevel);

		// now create children of the rootLogger
		final LoggerRepository rootRepos = rootLogger.getLoggerRepository();

		// controller
		final Logger controllerLogger = rootRepos.getLogger(LOGGER_NAME_CONTROLLER);
		final Level controllerLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_CONTROLLER_PREF);
		controllerLogger.setLevel(controllerLevel);

		// all non-controller loggers share a common parent
		final Logger nonControllerLogger = rootRepos.getLogger(LOGGER_NAME_NONCONTROLLER);
		nonControllerLogger.setLevel(rootLevel);
		final LoggerRepository nonControllerRepos = nonControllerLogger.getLoggerRepository();

		// plug-ins parent
		final Logger pluginsLogger = nonControllerRepos.getLogger(getPluginLoggerName());
		final Level pluginslevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_PLUGINS_PREF);
		pluginsLogger.setLevel(pluginslevel);

		// external tools parent
		final Logger toolslog = nonControllerRepos.getLogger(getToolLoggerName());
		final Level toolslevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_TOOLS_PREF);
		toolslog.setLevel(toolslevel);

		// actual core logger
		final Logger corelogger = nonControllerRepos.getLogger(getCoreLoggerName());
		final Level corelevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_CORE_PREF);
		corelogger.setLevel(corelevel);

		// actual plugin loggers
		final LoggerRepository piRepos = pluginsLogger.getLoggerRepository();
		final String[] plugins = getDefinedLogLevels();

		for (final String plugin : plugins) {
			final Logger logger = piRepos.getLogger(getPluginLoggerName(plugin));
			logger.setLevel(Level.toLevel(getLogLevel(plugin)));
			mLiveLoggerIds.add(logger.getName());
		}

		// actual tool loggers
		final LoggerRepository toolRepos = toolslog.getLoggerRepository();
		final String[] tools = getDefinedLogLevels();
		for (final String tool : tools) {
			final Logger logger = toolRepos.getLogger(getToolLoggerName(tool));
			logger.setLevel(Level.toLevel(getLogLevel(tool)));
			mLiveLoggerIds.add(logger.getName());
		}
	}

	private Level getLogLevelPreference(final String label) {
		return Level.toLevel(mPreferenceStore.getString(label));
	}

	/**
	 * Logger getLoggerById
	 *
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this id.
	 */
	private Logger getLoggerById(final String id) {
		return lookupLoggerInHierarchie(id);
	}

	/**
	 * boolean isExternalTool
	 *
	 * @param id
	 *            Internal logger id.
	 * @return <code>true</code> if and only if this id denotes an external tool.
	 */
	private static boolean isExternalTool(final String id) {
		return id.startsWith(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX);
	}

	/**
	 * This function tries to retrieve the correct logger with its associated log-levels based on its id.
	 *
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this internal id.
	 */
	private Logger lookupLoggerInHierarchie(final String id) {
		// it is the core
		if (id.equals(Activator.PLUGIN_ID)) {
			return Logger.getLogger(getCoreLoggerName());
		}

		// it is a controller or something that wants the controller logger
		assert mCurrentControllerName != null;
		if (id.equals(mCurrentControllerName) || id.equals(LOGGER_NAME_CONTROLLER)) {
			return Logger.getLogger(LOGGER_NAME_CONTROLLER);
		}

		// note: declared loggers are loggers with specified log levels

		// it is a declared one for a plugin
		final String pluginLoggerName = getPluginLoggerName(id);
		if (mLiveLoggerIds.contains(pluginLoggerName) && !isExternalTool(id)) {
			return Logger.getLogger(pluginLoggerName);
		}

		// it is a declared one for a tool
		final String toolLoggerName = getToolLoggerName(id);
		if (mLiveLoggerIds.contains(toolLoggerName) && isExternalTool(id)) {
			return Logger.getLogger(toolLoggerName);
		}

		// it is an undeclared external tool
		if (isExternalTool(id)) {
			return Logger.getLogger(getToolLoggerName());
		}

		// otherwise we assume it is some undeclared plugin
		return Logger.getLogger(getPluginLoggerName());
	}

	/**
	 * Returns the full name of a tool logger given the tools name.
	 */
	private String getToolLoggerName(final String tool) {
		return getToolLoggerName() + '.' + tool;
	}

	private String getToolLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + LOGGER_NAME_TOOLS;
	}

	/**
	 * Returns the full name of a plugin logger given the plugin name.
	 */
	private String getPluginLoggerName(final String plugin) {
		return getPluginLoggerName() + "." + plugin;
	}

	private String getPluginLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + LOGGER_NAME_PLUGINS;
	}

	/**
	 * Returns the full name of the core logger given the core name.
	 */
	private String getCoreLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + Activator.PLUGIN_ID;
	}

	/**
	 * String getLogLevel gets a log level for a certain plug-in
	 *
	 * @param id
	 *            the id of the plug in
	 * @return the log level or null if no log-level is directly associated
	 */
	private String getLogLevel(final String id) {
		final String[] pref = getLoggingDetailsPreference();
		for (final String string : pref) {
			if (string.startsWith(id + '=')) {
				return string.substring(string.lastIndexOf('=') + 1);
			}
		}
		return null;
	}

	private String[] getLoggingDetailsPreference() {
		return convert(mPreferenceStore.getString(CorePreferenceInitializer.PREFID_DETAILS));
	}

	private String[] getDefinedLogLevels() {
		final String[] pref = convert(mPreferenceStore.getString(CorePreferenceInitializer.PREFID_DETAILS));
		final String[] retVal = new String[pref.length];
		for (int i = 0; i < retVal.length; i++) {
			retVal[i] = pref[i].substring(0, pref[i].lastIndexOf('='));
		}
		return retVal;
	}

	public void setCurrentControllerID(final String name) {
		mCurrentControllerName = name;
	}

	@Override
	public void destroy() {
		assert sId == 1 : "There should be only one instance of Log4JLoggingService";
	}

	@Override
	public ILogger getLogger(final String pluginId) {
		return convert(getLoggerById(pluginId));
	}

	@Override
	public ILogger getLogger(final Class<?> clazz) {
		return getLogger(clazz.getName());
	}

	@Override
	public ILogger getLoggerForExternalTool(final String id) {
		return convert(getLoggerById(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX + id));
	}

	@Override
	public ILogger getControllerLogger() {
		return convert(getControllerRootLogger());
	}

	private Logger getLog4JRootLogger() {
		return Logger.getRootLogger();
	}

	private Logger getNonControllerRootLogger() {
		return Logger.getLogger(Log4JLoggingService.LOGGER_NAME_NONCONTROLLER);
	}

	private Logger getControllerRootLogger() {
		return Logger.getLogger(LOGGER_NAME_CONTROLLER);
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

	private static String[] convert(final String preferenceValue) {
		final StringTokenizer tokenizer =
				new StringTokenizer(preferenceValue, CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		final int tokenCount = tokenizer.countTokens();
		final String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}

	private static ILogger convert(final Logger logger) {
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

	public void store(final IToolchainStorage storage) {
		storage.putStorable(STORE_KEY, this);
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
			recreateLoggerHierarchie();
			reinitializeDefaultAppenders();
			reattachAppenders();
			getLoggerById(Activator.PLUGIN_ID).debug("Logger refreshed");
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
			result = prime * result + ((mWriter == null) ? 0 : mWriter.hashCode());
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
