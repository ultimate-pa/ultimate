package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import java.util.Arrays;

import org.eclipse.core.runtime.Platform;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;

/**
 * CorePreferenceInitializer implements UltimatePreferenceStore for
 * UltimateCore. It initializes the default values for preferences and provides
 * access to the preferences for the plugin
 * 
 * It has to contribute to the extension point
 * org.eclipse.core.runtime.preferences.initializer (see the plugin.xml)
 * 
 * @author Dietsch
 * 
 */
public class CorePreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {

				// Core
				new UltimatePreferenceItem<Boolean>(LABEL_SHOWUSABLEPARSER,
						VALUE_SHOWUSABLEPARSER_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_SHOWRESULTNOTIFIERPOPUP,
						VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT,
						PreferenceType.Boolean),

				// Log files
				new UltimatePreferenceItem<String>(DESC_LOGFILE, null,
						PreferenceType.Label),
				new UltimatePreferenceItem<Boolean>(LABEL_LOGFILE,
						VALUE_LOGFILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_APPEXLOGFILE,
						VALUE_APPEXLOGFILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_LOGFILE_NAME,
						VALUE_LOGFILE_NAME, PreferenceType.String),
				new UltimatePreferenceItem<String>(LABEL_LOGFILE_DIR,
						VALUE_LOGFILE_DIR, PreferenceType.Directory),

				// ModelManager
				new UltimatePreferenceItem<Boolean>(LABEL_MM_DROP_MODELS,
						VALUE_MM_DROP_MODELS, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_MM_TMPDIRECTORY,
						VALUE_MM_TMPDIRECTORY, PreferenceType.Directory),

				// Log levels
				new UltimatePreferenceItem<String>(LOGGING_PREFERENCES_DESC,
						null, PreferenceType.Label),
				new UltimatePreferenceItem<String>(LABEL_ROOT_PREF,
						VALUE_DEFAULT_LOGGING_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<String>(LABEL_CORE_PREF,
						VALUE_DEFAULT_LOGGING_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<String>(LABEL_CONTROLLER_PREF,
						VALUE_DEFAULT_LOGGING_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<String>(LABEL_PLUGINS_PREF,
						VALUE_DEFAULT_LOGGING_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<String>(LABEL_TOOLS_PREF,
						VALUE_DEFAULT_LOGGING_PREF, PreferenceType.String,
						null, new LogLevelValidator()),
				new UltimatePreferenceItem<String>(PREFID_DETAILS, "",
						PreferenceType.String, true, null, null),

		// Log levels for external tools

		// Plugin-specific log levels
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "General";
	}

	private class LogLevelValidator implements
			IUltimatePreferenceItemValidator<String> {
		@Override
		public boolean isValid(String value) {
			String s = value.toUpperCase();
			return s.equals(VALUE_TRACE_LOGGING_PREF)
					|| s.equals(VALUE_DEBUG_LOGGING_PREF)
					|| s.equals(VALUE_INFO_LOGGING_PREF)
					|| s.equals(VALUE_WARN_LOGGING_PREF)
					|| s.equals(VALUE_ERROR_LOGGING_PREF)
					|| s.equals(VALUE_FATAL_LOGGING_PREF);
		}

		@Override
		public String getInvalidValueErrorMessage(String value) {
			return INVALID_LOGLEVEL;
		}
	}

	public static final String PLUGINID = Activator.s_PLUGIN_ID;
	public static final String PLUGINNAME = Activator.s_PLUGIN_NAME;

	/**
	 * Preference Label/Value pairs
	 */

	// Core
	public static final String LABEL_SHOWUSABLEPARSER = "Show usable parsers";
	public static final boolean VALUE_SHOWUSABLEPARSER_DEFAULT = false;

	public static final String LABEL_SHOWRESULTNOTIFIERPOPUP = "Show Result in Pop-Up Window after Toolchain Execution";
	public static final boolean VALUE_SHOWRESULTNOTIFIERPOPUP_DEFAULT = false;

	// Log level
	public static final String DESC_LOGFILE = "The basic preferences for creating a log file (like enabled, name, directory)";

	public static final String LABEL_LOGFILE = "Create a Logfile";
	public static final boolean VALUE_LOGFILE = false;

	public static final String LABEL_APPEXLOGFILE = "Append to exisiting Logfile: ";
	public static final boolean VALUE_APPEXLOGFILE = false;

	public static final String LABEL_LOGFILE_NAME = "Name of the Logfile:";
	public static final String VALUE_LOGFILE_NAME = "ultimate.log";

	public static final String LABEL_LOGFILE_DIR = "Directory: (default: instance location):";
	public static final String VALUE_LOGFILE_DIR = Platform
			.getInstanceLocation().getURL().getPath();

	// Model manager
	public static final String LABEL_MM_DROP_MODELS = "Drop models when Ultimate exits";
	public static final boolean VALUE_MM_DROP_MODELS = true;

	public static final String LABEL_MM_TMPDIRECTORY = "Repository Directory";
	public static final String VALUE_MM_TMPDIRECTORY = System
			.getProperty("java.io.tmpdir");

	public static final String PREFID_ROOT = "ultimate.logging.root";
	public static final String PREFID_CORE = "ultimate.logging.core";
	public static final String PREFID_CONTROLLER = "ultimate.logging.controller";
	public static final String PREFID_TOOLS = "ultimate.logging.tools";
	public static final String PREFID_PLUGINS = "ultimate.logging.plugins";
	public static final String PREFID_DETAILS = "ultimate.logging.details";
	public static final String PREFID_TOOLDETAILS = "ultimate.logging.tooldetails";

	public static final String EXTERNAL_TOOLS_PREFIX = "external.";

	public static final String LABEL_ROOT_PREF = "Root Log Level";
	public static final String LABEL_TOOLS_PREF = "Log Level for External Tools";
	public static final String LABEL_CORE_PREF = "Log Level for Core Plugin";
	public static final String LABEL_CONTROLLER_PREF = "Log Level for Controller Plugin";
	public static final String LABEL_PLUGINS_PREF = "Log Level for Plugins";
	public static final String LABEL_PLUGIN_DETAIL_PREF = "Log Levels for Specific Plug-ins";

	public static final String VALUE_DEFAULT_LOGGING_PREF = "DEBUG";
	public static final String VALUE_FATAL_LOGGING_PREF = "FATAL";
	public static final String VALUE_ERROR_LOGGING_PREF = "ERROR";
	public static final String VALUE_WARN_LOGGING_PREF = "WARN";
	public static final String VALUE_INFO_LOGGING_PREF = "INFO";
	public static final String VALUE_DEBUG_LOGGING_PREF = "DEBUG";
	public static final String VALUE_TRACE_LOGGING_PREF = "TRACE";
	public static final String VALUE_DELIMITER_LOGGING_PREF = ";";
	public static final String[] VALUE_VALID_LOG_LEVELS = {
			VALUE_DEBUG_LOGGING_PREF, VALUE_ERROR_LOGGING_PREF,
			VALUE_FATAL_LOGGING_PREF, VALUE_INFO_LOGGING_PREF,
			VALUE_TRACE_LOGGING_PREF, VALUE_WARN_LOGGING_PREF };

	/**
	 * Messages
	 */
	public static final String INVALID_LOGLEVEL = "Valid levels: "
			+ Arrays.toString(VALUE_VALID_LOG_LEVELS);
	public static final String INVALID_ENTRY = "Entry has to be of the form: \"<plug-in id>=<log level>\"";
	public static final String INVALID_TOOL_ENTRY = "Entry has to be of the form: \"<tool id>=<log level>\"";
	public static final String LOGGING_PREFERENCES_DESC = "Specify log levels for the certail plug-ins.\nNote that there is a hierarchy and specifying a less strict level for children will have no effect";
	public static final String ALL_PLUGINS_PRESENT = "All entered Plug-ins are in fact present!";
	public static final String PLUGINS_NOT_PRESENT = "The following Plug-ins are not present at the moment: \n";
	public static final String EMPTY_STRING = "";

}
