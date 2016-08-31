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
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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

	private static final String APPENDER_NAME_CONSOLE = "ConsoleAppender";
	private static final String LOGGER_NAME_CONTROLLER = "controller";
	private static final String LOGGER_NAME_PLUGINS = "plugins";
	private static final String LOGGER_NAME_TOOLS = "tools";
	private static final String STORE_KEY = "LoggingService";

	private static int sId = 0;

	private final RcpPreferenceProvider mPreferenceStore;
	private List<String> mLiveLoggerIds;
	private ConsoleAppender mConsoleAppender;
	private final IPreferenceChangeListener mRefreshingListener;

	private final Set<Appender> mAdditionalAppenders;
	private String mCurrentControllerName;

	private final Map<String, FileAppender> mLogFiles;

	private Log4JLoggingService() {
		mLogFiles = new HashMap<>();
		mPreferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mAdditionalAppenders = new HashSet<>();

		// we remove the initial log4j console appender because we want to
		// replace it with our own
		Logger.getRootLogger().removeAppender(APPENDER_NAME_CONSOLE);

		final Enumeration<?> forgeinAppenders = Logger.getRootLogger().getAllAppenders();
		while (forgeinAppenders.hasMoreElements()) {
			final Appender appender = (Appender) forgeinAppenders.nextElement();
			mAdditionalAppenders.add(appender);
		}
		for (final Appender app : mAdditionalAppenders) {
			Logger.getRootLogger().removeAppender(app);
		}

		initializeAppenders();
		refreshPropertiesLoggerHierarchie();
		refreshPropertiesAppendLogFile();

		mRefreshingListener = new RefreshingPreferenceChangeListener();
		mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
		sId++;
	}

	public void refreshLoggingService() {
		initializeAppenders();
		refreshPropertiesLoggerHierarchie();
		refreshPropertiesAppendLogFile();
		getLoggerById(Activator.PLUGIN_ID).debug("Logger refreshed");
	}

	public void addAppender(final Appender appender) {
		mAdditionalAppenders.add(appender);
		Logger.getRootLogger().addAppender(appender);
	}

	public void removeAppender(final Appender appender) {
		mAdditionalAppenders.remove(appender);
		Logger.getRootLogger().removeAppender(appender);
	}

	private void initializeAppenders() {
		try {
			// clear all old appenders
			Logger.getRootLogger().removeAppender(mConsoleAppender);
			// we remove the initial log4j console appender because we want to
			// replace it with our own
			Logger.getRootLogger().removeAppender(APPENDER_NAME_CONSOLE);

			for (final Appender appender : mAdditionalAppenders) {
				Logger.getRootLogger().removeAppender(appender);
			}

			// first, handle console appender as we also configure it
			// defining format of logging output
			final PatternLayout layout =
					new PatternLayout(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN));

			// attaching output to console (stout)
			mConsoleAppender = new ConsoleAppender(layout);
			mConsoleAppender.setName(APPENDER_NAME_CONSOLE);
			Logger.getRootLogger().addAppender(mConsoleAppender);

			for (final Appender appender : mAdditionalAppenders) {
				// then, re-add all the other appenders
				Logger.getRootLogger().addAppender(appender);
			}

		} catch (final Exception ex) {
			System.err.println("Error while initializing logger: " + ex);
			ex.printStackTrace();
		}
	}

	private void refreshPropertiesAppendLogFile() {
		// if log-file should be used, it will be appended here
		if (mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE)) {
			final String logName = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_NAME);
			final String logDir = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_DIR);
			final String patternLayout = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN);
			final boolean append = mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_APPEXLOGFILE);
			try {
				addLogfile(patternLayout, logDir + File.separator + logName + ".log", append);
			} catch (final IOException e) {
				System.err.println("Error while appending log file to logger: " + e);
				e.printStackTrace();
			}
		}
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

	public static String getServiceKey() {
		return STORE_KEY;
	}

	/**
	 * Logger getLoggerById
	 *
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this id.
	 */
	public Logger getLoggerById(final String id) {
		return lookupLoggerInHierarchie(id);
	}

	/**
	 * boolean isExternalTool
	 *
	 * @param id
	 *            Internal logger id.
	 * @return <code>true</code> if and only if this id denotes an external tool.
	 */
	private boolean isExternalTool(final String id) {
		return id.startsWith(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX);
	}

	/**
	 * Logger lookupLoggerInHierarchie
	 *
	 * @param id
	 *            Internal logger id.
	 * @return Logger for this internal id.
	 */
	private Logger lookupLoggerInHierarchie(final String id) {
		// it is core
		if (id.equals(Activator.PLUGIN_ID)) {
			return Logger.getLogger(Activator.PLUGIN_ID);
		}
		// it is a controller
		assert mCurrentControllerName != null;
		if (id.equals(mCurrentControllerName)) {
			return Logger.getLogger(LOGGER_NAME_CONTROLLER);
		}
		// it is something that wants the contoller logger
		if (id.equals(LOGGER_NAME_CONTROLLER)) {
			return Logger.getLogger(LOGGER_NAME_CONTROLLER);
		}
		// it is a declared one for no tool
		if (mLiveLoggerIds.contains(LOGGER_NAME_PLUGINS + "." + id) && !isExternalTool(id)) {
			return Logger.getLogger(LOGGER_NAME_PLUGINS + "." + id);
		}
		// it is a declared one for a tool
		if (mLiveLoggerIds.contains(LOGGER_NAME_TOOLS + "." + id) && isExternalTool(id)) {
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
		mLiveLoggerIds = new LinkedList<>();
		final Logger rootLogger = Logger.getRootLogger();
		final String level = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_ROOT_PREF);
		rootLogger.setLevel(Level.toLevel(level));

		// now create children of the rootLogger

		// plug-ins
		final LoggerRepository rootRepos = rootLogger.getLoggerRepository();
		final Logger pluginsLogger = rootRepos.getLogger(LOGGER_NAME_PLUGINS);
		mLiveLoggerIds.add(LOGGER_NAME_PLUGINS);
		final String pluginslevel = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_PLUGINS_PREF);
		if (!pluginslevel.isEmpty()) {
			pluginsLogger.setLevel(Level.toLevel(pluginslevel));
		}

		// external tools
		final Logger toolslog = rootRepos.getLogger(LOGGER_NAME_TOOLS);
		mLiveLoggerIds.add(LOGGER_NAME_TOOLS);
		final String toolslevel = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_TOOLS_PREF);
		if (!toolslevel.isEmpty()) {
			toolslog.setLevel(Level.toLevel(toolslevel));
		}

		// controller
		final Logger controllogger = rootRepos.getLogger(LOGGER_NAME_CONTROLLER);
		final String controllevel = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_CONTROLLER_PREF);
		if (!controllevel.isEmpty()) {
			controllogger.setLevel(Level.toLevel(controllevel));
		}
		mLiveLoggerIds.add(LOGGER_NAME_CONTROLLER);

		// core
		final Logger corelogger = rootRepos.getLogger(Activator.PLUGIN_ID);
		final String corelevel = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_CORE_PREF);
		if (!corelevel.isEmpty()) {
			corelogger.setLevel(Level.toLevel(corelevel));
		}
		mLiveLoggerIds.add(Activator.PLUGIN_ID);

		// create children for plug-ins
		final LoggerRepository piRepos = pluginsLogger.getLoggerRepository();
		final String[] plugins = getDefinedLogLevels();

		for (final String plugin : plugins) {
			final Logger logger = piRepos.getLogger(LOGGER_NAME_PLUGINS + "." + plugin);
			logger.setLevel(Level.toLevel(getLogLevel(plugin)));
			mLiveLoggerIds.add(logger.getName());
		}

		// create child loggers for external tools
		final LoggerRepository toolRepos = toolslog.getLoggerRepository();
		final String[] tools = getDefinedLogLevels();
		for (final String tool : tools) {
			final Logger logger = toolRepos.getLogger(LOGGER_NAME_TOOLS + "." + tool);
			logger.setLevel(Level.toLevel(getLogLevel(tool)));
			mLiveLoggerIds.add(logger.getName());
		}
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

	private String[] convert(final String preferenceValue) {
		final StringTokenizer tokenizer =
				new StringTokenizer(preferenceValue, CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		final int tokenCount = tokenizer.countTokens();
		final String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
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
		return convert(getLoggerById(Log4JLoggingService.LOGGER_NAME_CONTROLLER));
	}

	@Override
	public void addLogfile(final String logPattern, final String absolutePath, final boolean append)
			throws IOException {
		final PatternLayout layout = new PatternLayout(logPattern);
		if (mLogFiles.containsKey(absolutePath)) {
			removeLogFile(absolutePath);
		}
		final FileAppender appender = new FileAppender(layout, absolutePath, append);
		Logger.getRootLogger().addAppender(appender);
		mLogFiles.put(absolutePath, appender);
	}

	@Override
	public void removeLogFile(final String absolutePath) {
		final FileAppender appender = mLogFiles.remove(absolutePath);
		if (appender == null) {
			return;
		}
		Logger.getRootLogger().removeAppender(appender);
		appender.close();
	}

	@Override
	public void addWriter(final Writer writer, final String logPattern) {
		final Appender appender = new Log4JAppenderWrapper(writer, logPattern);
		if (!mAdditionalAppenders.add(appender)) {
			// it is already added and the pattern cannot be changed without creating a new writer (removing closes the
			// writer)
			return;
		}
		Logger.getRootLogger().addAppender(appender);
	}

	@Override
	public void removeWriter(final Writer writer) {
		final Appender appender = new Log4JAppenderWrapper(writer, null);
		mAdditionalAppenders.remove(appender);
		Logger.getRootLogger().removeAppender(appender);
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

	private final class RefreshingPreferenceChangeListener implements IPreferenceChangeListener {
		// FIXME: Care! Check which properties are relevant for logging and
		// exactly when we have to reload
		// we do not care what property changes, we just reload the logging
		// stuff every time

		private RefreshingPreferenceChangeListener() {

		}

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
			if (ek.equals(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)
					|| ek.equals(CorePreferenceInitializer.LABEL_LOGFILE)
					|| ek.equals(CorePreferenceInitializer.LABEL_LOGFILE_NAME)
					|| ek.equals(CorePreferenceInitializer.LABEL_LOGFILE_DIR)
					|| ek.equals(CorePreferenceInitializer.LABEL_APPEXLOGFILE)
					|| ek.equals(CorePreferenceInitializer.EXTERNAL_TOOLS_PREFIX)
					|| ek.equals(CorePreferenceInitializer.PREFID_ROOT)
					|| ek.equals(CorePreferenceInitializer.PREFID_PLUGINS)
					|| ek.equals(CorePreferenceInitializer.PREFID_TOOLS)
					|| ek.equals(CorePreferenceInitializer.PREFID_CONTROLLER)
					|| ek.equals(CorePreferenceInitializer.PREFID_CORE)
					|| ek.equals(CorePreferenceInitializer.PREFID_DETAILS)
					|| ek.equals(CorePreferenceInitializer.LABEL_ROOT_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_TOOLS_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_CORE_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_CONTROLLER_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_PLUGINS_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_PLUGIN_DETAIL_PREF)
					|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_DEBUG)
					|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_INFO)
					|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_WARNING)
					|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_ERROR)
					|| ek.equals(CorePreferenceInitializer.LABEL_COLOR_FATAL)) {
				// its relevant
			} else {
				// it does not concern us, just break
				return;
			}
			refreshLoggingService();
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
