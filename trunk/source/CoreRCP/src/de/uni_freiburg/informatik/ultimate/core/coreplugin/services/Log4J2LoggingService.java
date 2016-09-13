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
import java.net.URI;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.StringTokenizer;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.core.Appender;
import org.apache.logging.log4j.core.Filter;
import org.apache.logging.log4j.core.LoggerContext;
import org.apache.logging.log4j.core.appender.ConsoleAppender;
import org.apache.logging.log4j.core.appender.WriterAppender;
import org.apache.logging.log4j.core.config.Configuration;
import org.apache.logging.log4j.core.config.ConfigurationFactory;
import org.apache.logging.log4j.core.config.ConfigurationSource;
import org.apache.logging.log4j.core.config.LoggerConfig;
import org.apache.logging.log4j.core.config.Order;
import org.apache.logging.log4j.core.config.builder.api.AppenderComponentBuilder;
import org.apache.logging.log4j.core.config.builder.api.ConfigurationBuilder;
import org.apache.logging.log4j.core.config.builder.impl.BuiltConfiguration;
import org.apache.logging.log4j.core.config.plugins.Plugin;
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

	private static final String APPENDER_NAME_CONSOLE = "ConsoleAppender";
	private static final String APPENDER_NAME_LOGFILE = "LogfileAppender";
	private static final String APPENDER_NAME_CONTROLLER = "ControllerAppender";
	private static final String LOGGER_NAME_CONTROLLER = "controller";
	private static final String LOGGER_NAME_PLUGINS = "plugins";
	private static final String LOGGER_NAME_TOOLS = "tools";
	private static final String LOGGER_NAME_NONCONTROLLER = "noncontroller";

	/**
	 * Used to distinguish between loggers that were created using {@link #getLogger(String)} and using
	 * {@link #getLoggerForExternalTool(String)}.
	 */
	private static final String LOGGER_NAME_PREFIX_TOOLS = "external.";

	private static final String STORE_KEY = "LoggingService";

	private static int sId;

	private final RcpPreferenceProvider mPreferenceStore;
	private final IPreferenceChangeListener mRefreshingListener;
	private final Set<Appender> mRootAppenders;
	private final Set<Appender> mControllerAppenders;

	private final Set<String> mLiveLoggerIds;
	private String mCurrentControllerName;

	private Log4J2LoggingService() {
		mPreferenceStore = new RcpPreferenceProvider(Activator.PLUGIN_ID);
		mRootAppenders = new HashSet<>();
		mControllerAppenders = new HashSet<>();
		mLiveLoggerIds = new HashSet<>();

		recreateLoggerHierarchy();
		reinitializeDefaultAppenders();
		reattachAppenders();

		mRefreshingListener = new RefreshingPreferenceChangeListener();
		mPreferenceStore.addPreferenceChangeListener(mRefreshingListener);
		sId++;
	}

	@Override
	public void reloadLoggers() {
		recreateLoggerHierarchy();
		reinitializeDefaultAppenders();
		reattachAppenders();
		getLoggerById(Activator.PLUGIN_ID).debug("Logger refreshed");
	}

	private void reinitializeDefaultAppenders() {
		ConfigurationFactory.setConfigurationFactory(new Log4J2ConfigurationFactory(mPreferenceStore));
		mRootAppenders.clear();
		mControllerAppenders.clear();

		// TODO Layout

		// TODO Logfile
	}

	private void reattachAppenders() {
		reattachAppenders(getNonControllerRootLogger(), mRootAppenders);
		reattachAppenders(getControllerRootLogger(), mControllerAppenders);
	}

	private static void reattachAppenders(final Logger logger, final Collection<Appender> appenders) {
		for (final Appender appender : appenders) {
			// TODO Do something!
		}
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

	private void recreateLoggerHierarchy() {
		mLiveLoggerIds.clear();
		final Logger rootLogger = getLog4J2RootLogger();
	}

	private Logger getLog4J2RootLogger() {
		return LogManager.getRootLogger();
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
		// TODO

		final String writerName = getWriterName(writer);

		final LoggerContext context = LoggerContext.getContext(false);
		final Configuration config = context.getConfiguration();
		final PatternLayout layout = PatternLayout.createDefaultLayout(config);
		final Appender appender = WriterAppender.createAppender(layout, null, writer, writerName, false, true);
		appender.start();
		config.addAppender(appender);
		updateLoggers(appender, config);
	}

	private void updateLoggers(final Appender appender, final Configuration config) {
		final Level level = null;
		final Filter filter = null;
		for (final LoggerConfig loggerConfig : config.getLoggers().values()) {
			loggerConfig.addAppender(appender, level, filter);
		}
		config.getRootLogger().addAppender(appender, level, filter);
	}

	@Override
	public void removeWriter(final Writer writer) {
		final String writerName = getWriterName(writer);

		final LoggerContext context = LoggerContext.getContext(false);
		final Configuration config = context.getConfiguration();
		final Appender toRemove = config.getAppenders().get(writerName);
		assert toRemove != null;
		for (final org.apache.logging.log4j.core.Logger logger : context.getLoggers()) {
			logger.removeAppender(toRemove);
		}
	}

	private static String getWriterName(final Writer writer) {
		return writer.getClass().getSimpleName() + writer.hashCode();
	}

	@Override
	public void destroy() {
		assert sId == 1 : "There should be only one instance of Log4J2LoggingService";
	}

	private Logger getLoggerById(final String id) {
		return lookupLoggerInHierarchy(id);
	}

	private Logger lookupLoggerInHierarchy(final String id) {
		if (id.equals(Activator.PLUGIN_ID)) {
			return LogManager.getLogger(getCoreLoggerName());
		}

		assert mCurrentControllerName != null;
		if (id.equals(mCurrentControllerName) || id.equals(LOGGER_NAME_CONTROLLER)) {
			return LogManager.getLogger(LOGGER_NAME_CONTROLLER);
		}

		final String pluginLoggerName = getPluginLoggerName(id);
		if (mLiveLoggerIds.contains(pluginLoggerName) && !isExternalTool(id)) {
			return LogManager.getLogger(pluginLoggerName);
		}

		final String toolLoggerName = getToolLoggerName(id);
		if (mLiveLoggerIds.contains(toolLoggerName) && isExternalTool(id)) {
			return LogManager.getLogger(toolLoggerName);
		}

		if (isExternalTool(id)) {
			return LogManager.getLogger(getToolLoggerName());
		}

		return LogManager.getLogger(getPluginLoggerName());
	}

	private Logger getNonControllerRootLogger() {
		return LogManager.getLogger(LOGGER_NAME_NONCONTROLLER);
	}

	private Logger getControllerRootLogger() {
		return LogManager.getLogger(LOGGER_NAME_CONTROLLER);
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
		final StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
		        CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
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

	@Plugin(name = "Log4J2ConfigurationFactory", category = ConfigurationFactory.CATEGORY)
	@Order(50)
	private static final class Log4J2ConfigurationFactory extends ConfigurationFactory {

		private final RcpPreferenceProvider mPreferenceStore;

		Log4J2ConfigurationFactory(final RcpPreferenceProvider preferenceStore) {
			mPreferenceStore = preferenceStore;
		}

		static Configuration createConfiguration(final String name,
		        final ConfigurationBuilder<BuiltConfiguration> builder, final RcpPreferenceProvider preferenceStore) {
			builder.setConfigurationName(name);
			builder.setStatusLevel(Level.ERROR);
			builder.add(builder.newFilter("ThresholdFilter", Filter.Result.ACCEPT, Filter.Result.NEUTRAL)
			        .addAttribute("level", Level.DEBUG));

			// TODO: Check whether "Stdout" must be used here instead of APPENDER_NAME_CONSOLE.
			final AppenderComponentBuilder appenderBuilder = builder.newAppender(APPENDER_NAME_CONSOLE, "CONSOLE")
			        .addAttribute("target", ConsoleAppender.Target.SYSTEM_OUT);
			appenderBuilder.add(builder.newLayout("PatternLayout").addAttribute("pattern",
			        CorePreferenceInitializer.LABEL_LOG4J_PATTERN));
			appenderBuilder.add(builder.newFilter("MarkerFilter", Filter.Result.DENY, Filter.Result.NEUTRAL)
			        .addAttribute("marker", "FLOW"));
			builder.add(appenderBuilder);

			final boolean useLogFile = preferenceStore.getBoolean(CorePreferenceInitializer.LABEL_LOGFILE);

			if (useLogFile) {

				final String logName = preferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_NAME);
				final String logDir = preferenceStore.getString(CorePreferenceInitializer.LABEL_LOGFILE_DIR);
				final String append = (preferenceStore.getBoolean(CorePreferenceInitializer.LABEL_APPEXLOGFILE) ? "true"
				        : "false");
				final String absolutePath = logDir + File.separator + logName + ".log";

				final AppenderComponentBuilder logFileBuilder = builder.newAppender(APPENDER_NAME_LOGFILE, "FILE")
				        .addAttribute("fileName", absolutePath).addAttribute("append", append);
				logFileBuilder.add(builder.newLayout("PatternLayout").addAttribute("pattern",
				        CorePreferenceInitializer.LABEL_LOG4J_PATTERN));
				logFileBuilder.add(builder.newFilter("MarkerFilter", Filter.Result.DENY, Filter.Result.NEUTRAL)
				        .addAttribute("marker", "FLOW"));
				builder.add(logFileBuilder);
			}

			// TODO: Maybe change the name of the logger here.
			builder.add(builder.newLogger("org.apache.logging.log4j", Level.DEBUG)
			        .add(builder.newAppenderRef(APPENDER_NAME_CONSOLE)).addAttribute("additivity", false));
			builder.add(builder.newRootLogger(Level.ERROR).add(builder.newAppenderRef(APPENDER_NAME_CONSOLE)));

			if (useLogFile) {
				builder.add(builder.newLogger(APPENDER_NAME_LOGFILE, Level.DEBUG)
				        .add(builder.newAppenderRef(APPENDER_NAME_LOGFILE)).addAttribute("additivity", false));
			}

			return builder.build();
		}

		@Override
		protected String[] getSupportedTypes() {
			return new String[] { "*" };
		}

		@Override
		public Configuration getConfiguration(final ConfigurationSource source) {
			return getConfiguration(source.toString(), null);
		}

		@Override
		public Configuration getConfiguration(final String name, final URI configLocation) {
			final ConfigurationBuilder<BuiltConfiguration> builder = newConfigurationBuilder();
			return createConfiguration(name, builder, mPreferenceStore);
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
