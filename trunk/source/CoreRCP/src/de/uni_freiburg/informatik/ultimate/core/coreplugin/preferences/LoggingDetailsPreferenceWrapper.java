/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences
 * File:	LoggingDetailsPreferenceWrapper.java created on Feb 1, 2010 by Björn Buchhold
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
public class LoggingDetailsPreferenceWrapper {

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
	 * Return the logging details preference default.
	 */
	public static String[] getDefaultLoggingDetailsPreference() {
		return convert(prefStore
				.getDefaultString(IPreferenceConstants.PREFID_DETAILS));
	}

	/**
	 * Returns the logging details preference.
	 */
	public static String[] getLoggingDetailsPreference() {
		return convert(prefStore.getString(IPreferenceConstants.PREFID_DETAILS));
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
	public static void setLoggingDeatilsPreference(String[] elements) {
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < elements.length; i++) {
			buffer.append(elements[i]);
			buffer.append(IPreferenceConstants.VALUE_DELIMITER_LOGGING_PREF);
		}
		prefStore.setValue(IPreferenceConstants.PREFID_DETAILS, buffer
				.toString());
	}

	/**
	 * String getLogLevel gets a log level for a certain plug-in
	 * 
	 * @param id
	 *            the id of the plug in
	 * @return the log level or null if no log-level is directly associated
	 */
	public static String getLogLevel(String id) {
		String[] pref = getLoggingDetailsPreference();
		for (String string : pref) {
			if (string.startsWith(id + "=")) {
				return string.substring(string.lastIndexOf("=") + 1);
			}
		}
		return null;
	}

	public static String[] getAllKeys() {
		String[] pref = getLoggingDetailsPreference();
		String[] retVal = new String[pref.length];
		for (int i = 0; i < retVal.length; i++) {
			retVal[i] = pref[i].substring(0, pref[i].lastIndexOf("="));
		}
		return retVal;
	}
}
