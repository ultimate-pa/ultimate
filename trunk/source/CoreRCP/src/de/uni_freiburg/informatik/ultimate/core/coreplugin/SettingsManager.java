/*
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
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;

class SettingsManager {

	// TODO: Check if this works with multiple instances of plugins

	private final Logger mLogger;
	private HashMap<String, LogPreferenceChangeListener> mActivePreferenceListener;

	SettingsManager(Logger logger) {
		mLogger = logger;
		mActivePreferenceListener = new HashMap<String, LogPreferenceChangeListener>();
	}

	void checkPreferencesForActivePlugins(String pluginId, String pluginName) {
		attachLogPreferenceChangeListenerToPlugin(pluginId, pluginName);
		logDefaultPreferences(pluginId, pluginName);
	}

	void loadPreferencesFromFile(ICore core, String filename) {
		if (filename != null && !filename.isEmpty()) {
			mLogger.debug("--------------------------------------------------------------------------------");
			mLogger.info("Beginning loading settings from " + filename);
			if (mLogger.isDebugEnabled()) {
				mLogger.info("Preferences different from defaults before loading file:");
				logPreferencesDifferentFromDefaults(core);
			}

			try {
				final FileInputStream fis = new FileInputStream(filename);
				final IStatus status = UltimatePreferenceStore.importPreferences(fis);
				if (!status.isOK()) {
					mLogger.warn("Failed to load preferences. Status is: " + status);
					mLogger.warn("Did not attach debug property logger");
				} else {
					mLogger.info("Loading preferences was successful");
				}
				mLogger.info("Preferences different from defaults after loading the file:");
				logPreferencesDifferentFromDefaults(core);
			} catch (Exception e) {
				mLogger.error("Could not load preferences because of exception: ", e);
				mLogger.warn("Did not attach debug property logger");
			} finally {
				mLogger.debug("--------------------------------------------------------------------------------");
			}
		} else {
			mLogger.info("Loading settings from empty filename is not possible");
		}
	}

	private void logPreferencesDifferentFromDefaults(ICore core) {
		boolean isSomePluginDifferent = false;
		for (final IUltimatePlugin plugin : core.getRegisteredUltimatePlugins()) {
			final String pluginId = plugin.getPluginID();
			final String[] delta = new UltimatePreferenceStore(pluginId).getDeltaPreferencesStrings();
			if (delta != null && delta.length > 0) {
				isSomePluginDifferent = true;
				mLogger.info("Preferences of " + plugin.getPluginName() + " differ from their defaults:");
				for (final String setting : delta) {
					mLogger.info(" * " + setting);
				}
			}
		}
		if (!isSomePluginDifferent) {
			mLogger.info("All preferences are set to their defaults");
		}
	}

	void savePreferences(ICore core, String filename) {
		if (filename == null || filename.isEmpty()) {
			return;
		}
		mLogger.info("Saving preferences to file " + filename);
		try {
			final File outputFile = new File(filename);
			if (outputFile.isFile() && outputFile.exists()) {
				outputFile.delete();
			}
			final FileOutputStream fis = new FileOutputStream(filename);

			for (final IUltimatePlugin plugin : core.getRegisteredUltimatePlugins()) {
				new UltimatePreferenceStore(plugin.getPluginID()).exportPreferences(fis);
			}

			fis.flush();
			fis.close();
		} catch (FileNotFoundException e) {
			mLogger.error("Saving preferences failed with exception: ", e);
		} catch (IOException e) {
			mLogger.error("Saving preferences failed with exception: ", e);
		} catch (CoreException e) {
			mLogger.error("Saving preferences failed with exception: ", e);
		}
	}

	void resetPreferences(ICore core) {
		mLogger.info("Resetting all preferences to default values...");
		for (IUltimatePlugin plugin : core.getRegisteredUltimatePlugins()) {
			UltimatePreferenceInitializer preferences = plugin.getPreferences();
			if (preferences != null) {
				mLogger.info("Resetting " + plugin.getPluginName() + " preferences to default values");
				preferences.resetDefaults();
			} else {
				mLogger.info(plugin.getPluginName() + " provides no preferences, ignoring...");
			}

		}
		mLogger.info("Finished resetting all preferences to default values...");
	}

	private void logDefaultPreferences(String pluginID, String pluginName) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		UltimatePreferenceStore ups = new UltimatePreferenceStore(pluginID);
		try {
			IEclipsePreferences defaults = ups.getDefaultEclipsePreferences();
			String prefix = "[" + pluginName + " (Current)] Preference \"";
			for (String key : defaults.keys()) {
				mLogger.debug(prefix + key + "\" = " + ups.getString(key, "NOT DEFINED"));
			}
		} catch (BackingStoreException e) {
			mLogger.debug("An exception occurred during printing of default preferences for plugin " + pluginName + ":"
					+ e.getMessage());
		}
	}

	/**
	 * Attaches Listener to all preferences and all scopes of all plugins to notify developers about changing
	 * preferences
	 * 
	 * @param pluginId
	 */
	private void attachLogPreferenceChangeListenerToPlugin(String pluginId, String pluginName) {

		LogPreferenceChangeListener instanceListener = retrieveListener(pluginId, pluginName, "Instance");
		LogPreferenceChangeListener configListener = retrieveListener(pluginId, pluginName, "Configuration");
		LogPreferenceChangeListener defaultListener = retrieveListener(pluginId, pluginName, "Default");

		InstanceScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(instanceListener);
		InstanceScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(instanceListener);

		ConfigurationScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(configListener);
		ConfigurationScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(configListener);

		DefaultScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(defaultListener);
		DefaultScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(defaultListener);
	}

	private LogPreferenceChangeListener retrieveListener(String pluginID, String pluginName, String scope) {
		String listenerID = pluginID + scope;
		if (mActivePreferenceListener.containsKey(listenerID)) {
			return mActivePreferenceListener.get(listenerID);
		} else {
			LogPreferenceChangeListener listener = new LogPreferenceChangeListener(scope, pluginID, pluginName);
			mActivePreferenceListener.put(listenerID, listener);
			return listener;
		}
	}

	class LogPreferenceChangeListener implements IPreferenceChangeListener {

		private final String mScope;
		private final UltimatePreferenceStore mPreferences;
		private final String mPrefix;

		public LogPreferenceChangeListener(String scope, String pluginID, String pluginName) {
			mScope = scope;
			mPreferences = new UltimatePreferenceStore(pluginID);
			mPrefix = "[" + pluginName + " (" + mScope + ")] Preference \"";
		}

		@Override
		public void preferenceChange(PreferenceChangeEvent event) {
			mLogger.debug(mPrefix + event.getKey() + "\" changed: " + event.getOldValue() + " -> " + event.getNewValue()
					+ " (actual value in store: " + mPreferences.getString(event.getKey()) + ")");
		}
	}

}
