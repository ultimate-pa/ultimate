/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences
 * File:	LoggingDetailsPreferenceWrapper.java created on Feb 1, 2010 by Bj�rn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import java.util.StringTokenizer;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * LoggingDetailsPreferenceWrapper
 * 
 * @author Björn Buchhold
 * 
 */
public class LoggingToolDetailsPreferenceWrapper {

	private static IPreferenceStore prefStore = new ScopedPreferenceStore(
			new InstanceScope(), Activator.s_PLUGIN_ID);

	/**
	 * getter for field prefStore
	 * 
	 * @return the prefStore
	 */
	public static IPreferenceStore getPrefStore() {
		return prefStore;
	}

	/**
	 * Return the logging tool details preference default.
	 */
	public static String[] getDefaultLoggingToolDetailsPreference() {
		return convert(prefStore
				.getDefaultString(IPreferenceConstants.PREFID_TOOLDETAILS));
	}

	/**
	 * Returns the logging tool details preference.
	 */
	public static String[] getLoggingToolDetailsPreference() {
		return convert(prefStore
				.getString(IPreferenceConstants.PREFID_TOOLDETAILS));
	}

	/**
	 * Converts IPreferenceConstants.VALUE_DELIMITER_LOGGING_PREF delimited
	 * String to a String array.
	 */
	private static String[] convert(String preferenceValue) {
		StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
				IPreferenceConstants.VALUE_DELIMITER_LOGGING_PREF);
		int tokenCount = tokenizer.countTokens();
		String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}

	/**
	 * Sets the logging details preference.
	 */
	public static void setLoggingToolDeatilsPreference(String[] elements) {
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < elements.length; i++) {
			buffer.append(elements[i]);
			buffer.append(IPreferenceConstants.VALUE_DELIMITER_LOGGING_PREF);
		}
		prefStore.setValue(IPreferenceConstants.PREFID_TOOLDETAILS, buffer
				.toString());
	}

	/**
	 * String getLogLevel gets a log level for a certain external tool
	 * 
	 * @param toolId
	 *            the id of the external tool
	 * @return the log level or null if no log-level is directly associated
	 */
	public static String getLogLevel(String toolId) {
		String[] pref = getLoggingToolDetailsPreference();
		String id = toolId.substring(IPreferenceConstants.EXTERNAL_TOOLS_PREFIX.length());
		for (String string : pref) {
			if (string.startsWith(id + "=")) {
				return string.substring(string.lastIndexOf("=") + 1);
			}
		}
		return null;
	}

	/**
	 * 
	 * 
	 * @return Keys for all external tools.
	 */
	public static String[] getAllKeys() {
		String[] pref = getLoggingToolDetailsPreference();
		String[] retVal = new String[pref.length];
		for (int i = 0; i < retVal.length; i++) {
			retVal[i] = IPreferenceConstants.EXTERNAL_TOOLS_PREFIX
					+ pref[i].substring(0, pref[i].lastIndexOf("="));
		}
		return retVal;
	}

}
