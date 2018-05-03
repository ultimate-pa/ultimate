/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.util.RcpUtils;

/**
 * CorePreferenceInitializer implements UltimatePreferenceStore for UltimateCore. It initializes the default values for
 * preferences and provides access to the preferences for the plugin.
 *
 * It has to contribute to the extension point org.eclipse.core.runtime.preferences.initializer (see the plugin.xml).
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class CorePreferenceInitializer extends RcpPreferenceInitializer {

	public enum WitnessVerifierType {
		CPACHECKER
	}

	public static final String PLUGINID = Activator.PLUGIN_ID;
	public static final String PLUGINNAME = Activator.PLUGIN_NAME;

	/**
	 * Preference Label/Value pairs
	 */

	// Core
	public static final String LABEL_SHOWUSABLEPARSER = "Show usable parsers";
	public static final boolean VALUE_SHOWUSABLEPARSER_DEFAULT = false;

	public static final String LABEL_SHOWRESULTNOTIFIERPOPUP = "Show result in pop-up window after toolchain execution";
	public static final boolean VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT = false;

	public static final String LABEL_BENCHMARK = "Generate benchmark results";
	public static final boolean VALUE_BENCHMARK_DEFAULT = true;

	public static final String LABEL_LONG_RESULT = "Show long description of results";
	public static final boolean VALUE_LONG_RESULT_DEFAULT = true;

	// Log4j pattern
	public static final String LABEL_LOG4J_PATTERN = "Logger pattern";
	/**
	 * Note that this log pattern consumes quite some cycles. Replacing it with "%-5p: %m%n" is advised for more
	 * performance.
	 */
	public static final String VALUE_LOG4J_PATTERN = "[%d{ISO8601} %-5p L%-5.5L %20.20C{1}]: %m%n";

	public static final String LABEL_LOG4J_CONTROLLER_PATTERN = "UI logger pattern";
	public static final String VALUE_LOG4J_CONTROLLER_PATTERN = "%m%n";

	// Log level
	public static final String DESC_LOGFILE =
			"The basic preferences for creating a log file (like enabled, name, " + "directory)";

	public static final String LABEL_LOGFILE = "Create a Logfile";
	public static final boolean VALUE_LOGFILE = false;

	public static final String LABEL_APPEXLOGFILE = "Append to exisiting log file";
	public static final boolean VALUE_APPEXLOGFILE = false;

	public static final String LABEL_LOGFILE_NAME = "Name of the log file";
	public static final String VALUE_LOGFILE_NAME = "ultimate.log";

	public static final String LABEL_LOGFILE_DIR = "Directory (default: instance location)";
	public static final String VALUE_LOGFILE_DIR;

	// Log colours
	public static final String LABEL_COLOR_DEBUG = "Debug log message color";
	public static final String DEFAULT_VALUE_COLOR_DEBUG = "223,223,223";

	public static final String LABEL_COLOR_INFO = "Info log message color";
	public static final String DEFAULT_VALUE_COLOR_INFO = "255,255,255";

	public static final String LABEL_COLOR_WARNING = "Warning log message color";
	public static final String DEFAULT_VALUE_COLOR_WARNING = "223,223,95";

	public static final String LABEL_COLOR_ERROR = "Error log message color";
	public static final String DEFAULT_VALUE_COLOR_ERROR = "255,85,85";

	public static final String LABEL_COLOR_FATAL = "Fatal log message color";
	public static final String DEFAULT_VALUE_COLOR_FATAL = "255,85,85";

	// Model manager
	public static final String LABEL_DROP_MODELS = "Drop models when Ultimate exits";
	public static final boolean VALUE_DROP_MODELS = true;

	public static final String LABEL_TMP_DIRECTORY = "Repository directory";
	public static final String VALUE_TMP_DIRECTORY;

	public static final String LABEL_LOGLEVEL_ROOT = "ultimate.logging.root";
	public static final String LABEL_LOGLEVEL_CORE = "ultimate.logging.core";
	public static final String LABEL_LOGLEVEL_CONTROLLER = "ultimate.logging.controller";
	public static final String LABEL_LOGLEVEL_TOOLS = "ultimate.logging.tools";
	public static final String LABEL_LOGLEVEL_PLUGINS = "ultimate.logging.plugins";
	public static final String LABEL_LOGLEVEL_PLUGIN_SPECIFIC = "ultimate.logging.details";
	public static final String LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC = "ultimate.logging.tooldetails";

	public static final String LABEL_ROOT_PREF = "Root log level";
	public static final String LABEL_TOOLS_PREF = "Log level for external tools";
	public static final String LABEL_CORE_PREF = "Log level for core plugin";
	public static final String LABEL_CONTROLLER_PREF = "Log level for controller plugin";
	public static final String LABEL_PLUGINS_PREF = "Log level for plugins";
	public static final String LABEL_PLUGIN_DETAIL_PREF = "Log levels for specific plugins";

	public static final String DEFAULT_VALUE_ROOT_PREF = "DEBUG";
	public static final String DEFAULT_VALUE_TOOLS_PREF = "WARN";
	public static final String DEFAULT_VALUE_CORE_PREF = "INFO";
	public static final String DEFAULT_VALUE_CONTROLLER_PREF = "INFO";
	public static final String DEFAULT_VALUE_PLUGINS_PREF = "INFO";

	public static final String VALUE_FATAL_LOGGING_PREF = "FATAL";
	public static final String VALUE_ERROR_LOGGING_PREF = "ERROR";
	public static final String VALUE_WARN_LOGGING_PREF = "WARN";
	public static final String VALUE_INFO_LOGGING_PREF = "INFO";
	public static final String VALUE_DEBUG_LOGGING_PREF = "DEBUG";
	public static final String VALUE_TRACE_LOGGING_PREF = "TRACE";
	public static final String VALUE_DELIMITER_LOGGING_PREF = ";";
	public static final String[] VALUE_VALID_LOG_LEVELS = { VALUE_DEBUG_LOGGING_PREF, VALUE_ERROR_LOGGING_PREF,
			VALUE_FATAL_LOGGING_PREF, VALUE_INFO_LOGGING_PREF, VALUE_TRACE_LOGGING_PREF, VALUE_WARN_LOGGING_PREF };

	public static final String LABEL_TIMEOUT = "Toolchain timeout in seconds";
	private static final int VALUE_TIMEOUT = 0;
	private static final String DESC_TIMEOUT =
			"Specify the time in seconds after which Ultimate will terminate due to a timeout. The value has to be larger or equal to 0. A value of 0 disables the timeout.";

	/**
	 * Messages
	 */
	public static final String INVALID_LOGLEVEL = "Valid levels: " + Arrays.toString(VALUE_VALID_LOG_LEVELS);
	public static final String INVALID_ENTRY = "Entry has to be of the form: \"<plug-in id>=<log level>\"";
	public static final String INVALID_TOOL_ENTRY = "Entry has to be of the form: \"<tool id>=<log level>\"";
	public static final String INVALID_WITNESSVERIFCATION_SETTING =
			"You must enable generation and writing of " + "witness results before you can verify them";
	public static final String LOGGING_PREFERENCES_DESC = "Specify log levels for the certail plugins.\n"
			+ "Note that there is a hierarchy and specifying a less strict level for children will have no effect";
	public static final String ALL_PLUGINS_PRESENT = "All entered plugins are in fact present!";
	public static final String PLUGINS_NOT_PRESENT = "The following plugins are not present at the moment: \n";
	public static final String EMPTY_STRING = "";

	static {
		final String tmpDir = System.getProperty("java.io.tmpdir");
		final String instLoc = RcpUtils.getInstanceLocationPath();
		if (instLoc == null) {
			VALUE_LOGFILE_DIR = tmpDir;
		} else {
			VALUE_LOGFILE_DIR = instLoc;
		}
		VALUE_TMP_DIRECTORY = tmpDir;
	}

	public CorePreferenceInitializer() {
		super(Activator.PLUGIN_ID, "General");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {

				// Core
				new UltimatePreferenceItem<>(LABEL_SHOWUSABLEPARSER, VALUE_SHOWUSABLEPARSER_DEFAULT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SHOWRESULTNOTIFIERPOPUP, VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_BENCHMARK, VALUE_BENCHMARK_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LONG_RESULT, VALUE_LONG_RESULT_DEFAULT, PreferenceType.Boolean),

				// Log files
				new UltimatePreferenceItem<String>(DESC_LOGFILE, null, PreferenceType.Label),
				new UltimatePreferenceItem<>(LABEL_LOGFILE, VALUE_LOGFILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_APPEXLOGFILE, VALUE_APPEXLOGFILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_LOGFILE_NAME, VALUE_LOGFILE_NAME, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_LOGFILE_DIR, VALUE_LOGFILE_DIR, PreferenceType.Directory),

				// ModelManager
				new UltimatePreferenceItem<>(LABEL_DROP_MODELS, VALUE_DROP_MODELS, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_TMP_DIRECTORY, VALUE_TMP_DIRECTORY, PreferenceType.Directory),

				new UltimatePreferenceItem<>(LABEL_LOG4J_PATTERN, VALUE_LOG4J_PATTERN, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_LOG4J_CONTROLLER_PATTERN, VALUE_LOG4J_CONTROLLER_PATTERN,
						PreferenceType.String),

				// Log levels
				new UltimatePreferenceItem<String>(LOGGING_PREFERENCES_DESC, null, PreferenceType.Label),
				new UltimatePreferenceItem<>(LABEL_ROOT_PREF, DEFAULT_VALUE_ROOT_PREF, PreferenceType.String, null,
						new LogLevelValidator()),
				new UltimatePreferenceItem<>(LABEL_CORE_PREF, DEFAULT_VALUE_CORE_PREF, PreferenceType.String, null,
						new LogLevelValidator()),
				new UltimatePreferenceItem<>(LABEL_CONTROLLER_PREF, DEFAULT_VALUE_CONTROLLER_PREF,
						PreferenceType.String, null, new LogLevelValidator()),
				new UltimatePreferenceItem<>(LABEL_PLUGINS_PREF, DEFAULT_VALUE_PLUGINS_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<>(LABEL_TOOLS_PREF, DEFAULT_VALUE_TOOLS_PREF, PreferenceType.String, null,
						new LogLevelValidator()),
				new UltimatePreferenceItem<>(LABEL_LOGLEVEL_PLUGIN_SPECIFIC, "", PreferenceType.String, null, true,
						null, null),

				// Log colours
				new UltimatePreferenceItem<>(LABEL_COLOR_DEBUG, DEFAULT_VALUE_COLOR_DEBUG, PreferenceType.Color),
				new UltimatePreferenceItem<>(LABEL_COLOR_INFO, DEFAULT_VALUE_COLOR_INFO, PreferenceType.Color),
				new UltimatePreferenceItem<>(LABEL_COLOR_WARNING, DEFAULT_VALUE_COLOR_WARNING, PreferenceType.Color),
				new UltimatePreferenceItem<>(LABEL_COLOR_ERROR, DEFAULT_VALUE_COLOR_ERROR, PreferenceType.Color),
				new UltimatePreferenceItem<>(LABEL_COLOR_FATAL, DEFAULT_VALUE_COLOR_FATAL, PreferenceType.Color),

				// Toolchain
				new UltimatePreferenceItem<>(LABEL_TIMEOUT, VALUE_TIMEOUT, DESC_TIMEOUT, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, Integer.MAX_VALUE)), };
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	private static final class LogLevelValidator implements IUltimatePreferenceItemValidator<String> {
		@Override
		public boolean isValid(final String value) {
			final String upper = value.toUpperCase();
			for (final String validValue : VALUE_VALID_LOG_LEVELS) {
				if (validValue.equals(upper)) {
					return true;
				}
			}
			return false;
		}

		@Override
		public String getInvalidValueErrorMessage(final String value) {
			return INVALID_LOGLEVEL;
		}
	}
}
