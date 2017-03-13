/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.io.File;
import java.io.Writer;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.Appender;
import org.apache.logging.log4j.core.Filter.Result;
import org.apache.logging.log4j.core.LoggerContext;
import org.apache.logging.log4j.core.appender.ConsoleAppender;
import org.apache.logging.log4j.core.appender.ConsoleAppender.Target;
import org.apache.logging.log4j.core.appender.FileAppender;
import org.apache.logging.log4j.core.appender.WriterAppender;
import org.apache.logging.log4j.core.config.AppenderRef;
import org.apache.logging.log4j.core.config.Configuration;
import org.apache.logging.log4j.core.config.Configurator;
import org.apache.logging.log4j.core.config.LoggerConfig;
import org.apache.logging.log4j.core.config.builder.api.ConfigurationBuilder;
import org.apache.logging.log4j.core.config.builder.api.ConfigurationBuilderFactory;
import org.apache.logging.log4j.core.config.builder.impl.BuiltConfiguration;
import org.apache.logging.log4j.core.filter.ThresholdFilter;
import org.apache.logging.log4j.core.layout.PatternLayout;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;

public final class Log4J2LoggingService implements IStorable, ILoggingService {

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

	private static final String LOGGER_NAME_CONTROLLER = "controller";
	private static final String LOGGER_NAME_PLUGINS = "plugins";
	private static final String LOGGER_NAME_TOOLS = "tools";
	private static final String LOGGER_NAME_NONCONTROLLER = "noncontroller";

	private static final String APPENDER_NAME_CONSOLE = "ConsoleAppender";
	private static final String APPENDER_NAME_LOGFILE = "LogfileAppender";
	private static final String APPENDER_NAME_CONTROLLER = "ControllerAppender";

	/**
	 * Used to distinguish between loggers that were created using {@link #getLogger(String)} and using
	 * {@link #getLoggerForExternalTool(String)}.
	 */
	private static final String LOGGER_NAME_PREFIX_TOOLS = "external.";

	private static final String STORE_KEY = "LoggingService";

	private static int sId;

	private final RcpPreferenceProvider mPreferenceStore;
	private final IPreferenceChangeListener mRefreshingListener;

	private Set<String> mLiveLoggerIds;
	private String mCurrentControllerName;

	private final LoggerContext mContext;
	private final Configuration mConfig;

	private final Set<Appender> mRootAppenders;
	private final Set<Appender> mControllerAppenders;

	private Appender mConsoleAppender;
	private Appender mControllerAppender;
	private Appender mFileAppender;

	private final Map<String, AppenderRef> mAppenderReferences;

	private Log4J2LoggingService() {
		mPreferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mLiveLoggerIds = new HashSet<>();

		mRootAppenders = new HashSet<>();
		mControllerAppenders = new HashSet<>();

		mAppenderReferences = new HashMap<>();

		mContext = initializeConfiguration();
		mConfig = mContext.getConfiguration();

		recreateLoggerHierarchy();
		mContext.updateLoggers();

		mRefreshingListener = new RefreshingPreferenceChangeListener();
		mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
		sId++;
	}

	@Override
	public void reloadLoggers() {
		recreateLoggerHierarchy();
		mContext.updateLoggers();
		getLoggerById(Activator.PLUGIN_ID).debug("Logger refreshed");
	}

	private void recreateLoggerHierarchy() {
		mLiveLoggerIds = new HashSet<>();

		mConfig.getAppenders().clear();

		reinitializeDefaultConsoleAppenders();
		reinitializeFileAppender();

		final AppenderRef[] refs =
				mAppenderReferences.values().toArray(new AppenderRef[mAppenderReferences.values().size()]);

		final Level rootLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_ROOT_PREF);
		final LoggerConfig rootLoggerConfig = mConfig.getRootLogger();
		rootLoggerConfig.setLevel(Level.ALL);
		rootLoggerConfig.addFilter(ThresholdFilter.createFilter(rootLevel, Result.ACCEPT, Result.NEUTRAL));
		rootLoggerConfig.addAppender(mConsoleAppender, rootLoggerConfig.getLevel(), rootLoggerConfig.getFilter());

		// create the children of the rootLogger

		// controller
		final Level controllerLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_CONTROLLER_PREF);
		final LoggerConfig controllerLoggerConfig =
				LoggerConfig.createLogger(true, controllerLevel, LOGGER_NAME_CONTROLLER, "true", refs, null, mConfig,
						ThresholdFilter.createFilter(controllerLevel, Result.ACCEPT, Result.NEUTRAL));
		mConfig.addLogger(LOGGER_NAME_CONTROLLER, controllerLoggerConfig);

		// all non-controller loggers share a common parent
		final LoggerConfig nonControllerLoggerConfig = LoggerConfig.createLogger(true, rootLevel,
				LOGGER_NAME_NONCONTROLLER, "true", refs, null, mConfig, null);
		mConfig.addLogger(LOGGER_NAME_NONCONTROLLER, nonControllerLoggerConfig);

		// plug-ins parent
		final Level pluginsLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_PLUGINS_PREF);
		final LoggerConfig pluginsParentLoggerConfig =
				LoggerConfig.createLogger(true, pluginsLevel, getPluginLoggerName(), "true", refs, null, mConfig, null);
		mConfig.addLogger(getPluginLoggerName(), pluginsParentLoggerConfig);

		// external tools parent
		final Level toolsLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_TOOLS_PREF);
		final LoggerConfig externalToolsLoggerConfig =
				LoggerConfig.createLogger(true, toolsLevel, getToolLoggerName(), "true", refs, null, mConfig, null);
		mConfig.addLogger(getToolLoggerName(), externalToolsLoggerConfig);

		// actual core logger
		final Level coreLevel = getLogLevelPreference(CorePreferenceInitializer.LABEL_CORE_PREF);
		final LoggerConfig coreLoggerConfig =
				LoggerConfig.createLogger(true, coreLevel, getCoreLoggerName(), "true", refs, null, mConfig, null);
		mConfig.addLogger(getCoreLoggerName(), coreLoggerConfig);

		// actual plugin loggers
		final String[] plugins = getIdsWithDefinedLogLevels(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC);

		for (final String plugin : plugins) {
			final String loggerName = getPluginLoggerName(plugin);
			final Level pluginLevel = getLogLevel(plugin);
			final LoggerConfig pluginLoggerConfig =
					LoggerConfig.createLogger(true, pluginLevel, loggerName, "true", refs, null, mConfig, null);
			mConfig.addLogger(loggerName, pluginLoggerConfig);
			mLiveLoggerIds.add(loggerName);
		}

		// actual tool loggers
		final String[] tools =
				getIdsWithDefinedLogLevels(CorePreferenceInitializer.LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC);

		for (final String tool : tools) {
			final String loggerName = getToolLoggerName(tool);
			final Level toolLevel = getLogLevel(tool);
			final LoggerConfig toolLoggerConfig =
					LoggerConfig.createLogger(true, toolLevel, loggerName, "true", refs, null, mConfig, null);
			mConfig.addLogger(loggerName, toolLoggerConfig);
			mLiveLoggerIds.add(loggerName);
		}

		reattachAppenders();
	}

	private void reinitializeDefaultConsoleAppenders() {
		if (mConsoleAppender != null) {
			mConsoleAppender.stop();
			mConfig.getRootLogger().removeAppender(mConsoleAppender.getName());
			mAppenderReferences.remove(mConsoleAppender.getName());
			mConfig.getAppenders().remove(mConsoleAppender);
			mRootAppenders.remove(mConsoleAppender);
			mConsoleAppender = null;
		}

		final PatternLayout layout = PatternLayout.newBuilder()
				.withPattern(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)).build();

		mConsoleAppender = ConsoleAppender.createAppender(layout, null, Target.SYSTEM_OUT, APPENDER_NAME_CONSOLE, true,
				false, false);
		mConsoleAppender.start();
		mConfig.addAppender(mConsoleAppender);
		mAppenderReferences.put(mConsoleAppender.getName(),
				AppenderRef.createAppenderRef(mConsoleAppender.getName(), null, null));
		mRootAppenders.add(mConsoleAppender);

		if (mControllerAppender != null) {
			mControllerAppender.stop();
			mConfig.getLoggerConfig(LOGGER_NAME_CONTROLLER).removeAppender(mControllerAppender.getName());
			mAppenderReferences.remove(mControllerAppender.getName());
			mConfig.getAppenders().remove(mControllerAppender);
			mControllerAppenders.remove(mControllerAppender);
			mControllerAppender = null;
		}

		final PatternLayout controllerLayout = PatternLayout.newBuilder()
				.withPattern(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_CONTROLLER_PATTERN))
				.build();

		mControllerAppender = ConsoleAppender.createAppender(controllerLayout, null, Target.SYSTEM_OUT,
				APPENDER_NAME_CONTROLLER, true, false, false);
		mControllerAppender.start();
		mConfig.addAppender(mControllerAppender);
		mAppenderReferences.put(mControllerAppender.getName(),
				AppenderRef.createAppenderRef(mControllerAppender.getName(), null, null));
		mControllerAppenders.add(mControllerAppender);
	}

	private void reattachAppenders() {
		reattachAppenders(getNonControllerRootLogger(), mRootAppenders);
		reattachAppenders(getControllerRootLogger(), mControllerAppenders);
	}

	private void reattachAppenders(final Logger logger, final Collection<Appender> appenders) {
		final LoggerConfig loggerConfig = mConfig.getLoggerConfig(logger.getName());
		for (final Appender appender : appenders) {
			loggerConfig.removeAppender(appender.getName());
			loggerConfig.addAppender(appender, loggerConfig.getLevel(), loggerConfig.getFilter());
		}
	}

	private void reinitializeFileAppender() {
		// if log-file should be used, it will be appended here
		if (mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE)) {
			// if there is already a log file appender, we remove it.
			if (mFileAppender != null) {
				mFileAppender.stop();
				mConfig.getRootLogger().removeAppender(mFileAppender.getName());
				mConfig.getLoggerConfig(LOGGER_NAME_CONTROLLER).removeAppender(mFileAppender.getName());
				mAppenderReferences.remove(mFileAppender.getName());
				mConfig.getAppenders().remove(mFileAppender);
				mRootAppenders.remove(mFileAppender);
				mControllerAppenders.remove(mFileAppender);
				mFileAppender = null;
			}

			final PatternLayout layout = PatternLayout.newBuilder()
					.withPattern(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)).build();
			final String logName = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_NAME);
			final String logDir = mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_DIR);
			final Boolean append = mPreferenceStore.getBoolean(CorePreferenceInitializer.LABEL_APPEXLOGFILE);
			final String fileName =
					new StringBuilder().append(logDir).append(File.separator).append(logName).append(".log").toString();

			final String falsePredicate = "false";
			final String truePredicate = "true";

			mFileAppender = FileAppender.createAppender(fileName, append.toString(), falsePredicate,
					APPENDER_NAME_LOGFILE, truePredicate, truePredicate, falsePredicate, "8192", layout, null,
					falsePredicate, null, mConfig);
			mFileAppender.start();
			mConfig.addAppender(mFileAppender);
			mRootAppenders.add(mFileAppender);
			mControllerAppenders.add(mFileAppender);
		} else {
			if (mFileAppender != null) {
				mFileAppender.stop();
				mConfig.getRootLogger().removeAppender(mFileAppender.getName());
				mConfig.getLoggerConfig(LOGGER_NAME_CONTROLLER).removeAppender(mFileAppender.getName());
				mAppenderReferences.remove(mFileAppender.getName());
				mConfig.getAppenders().remove(mFileAppender);
				mRootAppenders.remove(mFileAppender);
				mControllerAppenders.remove(mFileAppender);
				mFileAppender = null;
			}
		}
	}

	private Level getLogLevel(final String id) {
		final String[] pref = getLoggingDetailsPreference();
		for (final String string : pref) {
			if (string.startsWith(id + '=')) {
				return Level.toLevel(string.substring(string.lastIndexOf('=') + 1));
			}
		}

		return null;
	}

	private String[] getLoggingDetailsPreference() {
		return convert(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC));
	}

	private String[] getIdsWithDefinedLogLevels(final String preferenceLabel) {
		final String[] pref = convert(mPreferenceStore.getString(preferenceLabel));
		final String[] retVal = new String[pref.length];
		for (int i = 0; i < pref.length; i++) {
			retVal[i] = pref[i].substring(0, pref[i].lastIndexOf('='));
		}
		return retVal;
	}

	private Level getLogLevelPreference(final String label) {
		final String level = mPreferenceStore.getString(label);
		assert level != null && !level.isEmpty();

		return Level.toLevel(level);
	}

	private static LoggerContext initializeConfiguration() {
		final ConfigurationBuilder<BuiltConfiguration> builder = ConfigurationBuilderFactory.newConfigurationBuilder();
		builder.setStatusLevel(Level.ERROR);
		builder.setConfigurationName("DefaultConfiguration");

		final LoggerContext returnContext = Configurator.initialize(builder.build());
		final org.apache.logging.log4j.core.Logger rootLogger = returnContext.getRootLogger();
		for (final Appender appender : rootLogger.getAppenders().values()) {
			rootLogger.removeAppender(appender);
		}

		return returnContext;
	}

	static Log4J2LoggingService getService(final IToolchainStorage storage) {
		assert storage != null;
		IStorable rtr = storage.getStorable(STORE_KEY);
		if (rtr == null) {
			rtr = new Log4J2LoggingService();
			storage.putStorable(STORE_KEY, rtr);
		}
		return (Log4J2LoggingService) rtr;
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
		return convert(getLoggerById(LOGGER_NAME_PREFIX_TOOLS + id));
	}

	@Override
	public ILogger getControllerLogger() {
		return convert(getControllerRootLogger());
	}

	@Override
	public Object getBacking(final ILogger logger, final Class<?> backingType) {
		if (logger == null || backingType == null) {
			return null;
		}
		if (Logger.class.isAssignableFrom(backingType) && logger instanceof Log4J2Wrapper) {
			final Log4J2Wrapper wrappedLogger = (Log4J2Wrapper) logger;
			return wrappedLogger.getBacking();
		}
		return null;
	}

	@Override
	public void addWriter(final Writer writer, final String logPattern) {
		final String writerName = getWriterName(writer);

		mRootAppenders.removeIf(app -> app.getName().equals(writerName));

		final PatternLayout layout = PatternLayout.newBuilder().withPattern(logPattern).build();

		final Appender appender = WriterAppender.createAppender(layout, null, writer, writerName, false, true);
		appender.start();
		mConfig.addAppender(appender);
		mRootAppenders.add(appender);

		mConfig.getRootLogger().addAppender(appender, mConfig.getRootLogger().getLevel(),
				mConfig.getRootLogger().getFilter());

		mContext.updateLoggers();
	}

	@Override
	public void removeWriter(final Writer writer) {
		final String writerName = getWriterName(writer);

		final Appender toRemove = mConfig.getAppenders().get(writerName);
		assert toRemove != null;
		assert mRootAppenders.contains(toRemove);

		toRemove.stop();

		mRootAppenders.remove(toRemove);
		mConfig.getRootLogger().removeAppender(toRemove.getName());
	}

	private static String getWriterName(final Writer writer) {
		return writer.getClass().getSimpleName() + writer.hashCode();
	}

	@Override
	public void destroy() {
		mPreferenceStore.removePreferenceChangeListener(mRefreshingListener);
		assert sId == 1 : "There should be only one instance of Log4J2LoggingService";
	}

	/**
	 * Returns the logger corresponding to the given ID.
	 *
	 * @param id
	 *            The ID of the logger.
	 * @return The corresponding logger.
	 */
	private Logger getLoggerById(final String id) {
		return lookupLoggerInHierarchy(id);
	}

	private Logger lookupLoggerInHierarchy(final String id) {
		if (id.equals(Activator.PLUGIN_ID)) {
			return mContext.getLogger(getCoreLoggerName());
		}

		// it is a controller or something that wants the controller logger
		assert mCurrentControllerName != null;
		if (id.equals(mCurrentControllerName) || id.equals(LOGGER_NAME_CONTROLLER)) {
			return mContext.getLogger(LOGGER_NAME_CONTROLLER);
		}

		final String pluginLoggerName = getPluginLoggerName(id);
		if (mLiveLoggerIds.contains(pluginLoggerName) && !isExternalTool(id)) {
			return mContext.getLogger(pluginLoggerName);
		}

		final String toolLoggerName = getToolLoggerName(id);
		if (mLiveLoggerIds.contains(toolLoggerName) && isExternalTool(id)) {
			return mContext.getLogger(toolLoggerName);
		}

		if (isExternalTool(id)) {
			return mContext.getLogger(getToolLoggerName());
		}

		return mContext.getLogger(getPluginLoggerName());
	}

	private Logger getNonControllerRootLogger() {
		return mContext.getLogger(LOGGER_NAME_NONCONTROLLER);
	}

	private Logger getControllerRootLogger() {
		return mContext.getLogger(LOGGER_NAME_CONTROLLER);
	}

	private static String getCoreLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + Activator.PLUGIN_ID;
	}

	private static String getPluginLoggerName(final String plugin) {
		return getPluginLoggerName() + '.' + plugin;
	}

	private static String getPluginLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + LOGGER_NAME_PLUGINS;
	}

	private static String getToolLoggerName(final String toolId) {
		return getToolLoggerName() + '.' + LOGGER_NAME_PREFIX_TOOLS + toolId;
	}

	private static String getToolLoggerName() {
		return LOGGER_NAME_NONCONTROLLER + '.' + LOGGER_NAME_TOOLS;
	}

	private static boolean isExternalTool(final String id) {
		return id.startsWith(LOGGER_NAME_PREFIX_TOOLS);
	}

	private static ILogger convert(final Logger logger) {
		return new Log4J2Wrapper(logger);
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
				return;
			}

			reloadLoggers();
		}
	}

	@Override
	public void setCurrentControllerID(final String name) {
		mCurrentControllerName = name;
	}

	@Override
	public void store(final IToolchainStorage storage) {
		storage.putStorable(STORE_KEY, this);
	}
}
