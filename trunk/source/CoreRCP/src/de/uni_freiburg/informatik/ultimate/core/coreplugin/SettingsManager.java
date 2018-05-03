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
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.PreferenceChangeEvent;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IUltimatePlugin;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceBinder;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;

/**
 * The SettingsManager initializes the default settings of all plugins as well as loading and saving settings of an
 * Ultimate instance.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class SettingsManager {

	// TODO: Check if this works with multiple instances of plugins

	private static final String SAVING_PREFERENCES_FAILED_WITH_EXCEPTION = "Saving preferences failed with exception: ";
	private final ILogger mLogger;
	private final Map<String, LogPreferenceChangeListener> mActivePreferenceListener;

	SettingsManager(final ILogger logger) {
		mLogger = logger;
		mActivePreferenceListener = new HashMap<>();
	}

	void registerPlugin(final IUltimatePlugin plugin) {
		if (plugin == null) {
			return;
		}

		final String pluginName = plugin.getPluginName();
		final IPreferenceInitializer prefs = plugin.getPreferences();
		if (prefs == null) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Plugin " + pluginName + " does not have preferences");
			}
			return;
		}
		final String pluginId = plugin.getPluginID();
		RcpPreferenceBinder.registerDefaultPreferences(pluginId, prefs.getPreferenceItems());
		attachLogPreferenceChangeListenerToPlugin(pluginId, pluginName);
		logDefaultPreferences(pluginId, pluginName);
	}

	void loadPreferencesFromFile(final ICore<RunDefinition> core, final String filename) {
		if (filename != null && !filename.isEmpty()) {
			mLogger.debug("--------------------------------------------------------------------------------");
			mLogger.info("Beginning loading settings from " + filename);
			if (mLogger.isDebugEnabled()) {
				mLogger.info("Preferences different from defaults before loading file:");
				logPreferencesDifferentFromDefaults(core);
			}

			try {
				final FileInputStream fis = new FileInputStream(filename);
				final IStatus status = RcpPreferenceProvider.importPreferences(fis);
				if (!status.isOK()) {
					mLogger.warn("Failed to load preferences. Status is: " + status);
				} else {
					mLogger.info("Loading preferences was successful");
				}
				mLogger.info("Preferences different from defaults after loading the file:");
				logPreferencesDifferentFromDefaults(core);
			} catch (IOException | CoreException e) {
				mLogger.error("Could not load preferences: " + e.getMessage());
			} finally {
				mLogger.debug("--------------------------------------------------------------------------------");
			}
		} else {
			mLogger.info("Loading settings from empty filename is not possible");
		}
	}

	private void logPreferencesDifferentFromDefaults(final ICore<RunDefinition> core) {
		boolean isSomePluginDifferent = false;
		for (final IUltimatePlugin plugin : core.getRegisteredUltimatePlugins()) {
			final String pluginId = plugin.getPluginID();
			final String[] delta = new RcpPreferenceProvider(pluginId).getDeltaPreferencesStrings();
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

	void savePreferences(final ICore<RunDefinition> core, final String filename) {
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
				new RcpPreferenceProvider(plugin.getPluginID()).exportPreferences(fis);
			}

			fis.flush();
			fis.close();
		} catch (final FileNotFoundException e) {
			mLogger.error(SAVING_PREFERENCES_FAILED_WITH_EXCEPTION, e);
		} catch (final IOException e) {
			mLogger.error(SAVING_PREFERENCES_FAILED_WITH_EXCEPTION, e);
		} catch (final CoreException e) {
			mLogger.error(SAVING_PREFERENCES_FAILED_WITH_EXCEPTION, e);
		}
	}

	void resetPreferences(final ICore<RunDefinition> core) {
		mLogger.info("Resetting all preferences to default values...");
		for (final IUltimatePlugin plugin : core.getRegisteredUltimatePlugins()) {
			final IPreferenceInitializer preferences = plugin.getPreferences();
			if (preferences != null) {
				mLogger.info("Resetting " + plugin.getPluginName() + " preferences to default values");
				RcpPreferenceBinder.resetToDefaultPreferences(plugin.getPluginID(), preferences.getPreferenceItems());
			} else {
				mLogger.info(plugin.getPluginName() + " provides no preferences, ignoring...");
			}

		}
		mLogger.info("Finished resetting all preferences to default values...");
	}

	private void logDefaultPreferences(final String pluginID, final String pluginName) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		final RcpPreferenceProvider ups = new RcpPreferenceProvider(pluginID);
		try {
			final IEclipsePreferences defaults = ups.getDefaultEclipsePreferences();
			final String prefix = "[" + pluginName + " (Current)] Preference \"";
			for (final String key : defaults.keys()) {
				mLogger.debug(prefix + key + "\" = " + ups.getString(key, "NOT DEFINED"));
			}
		} catch (final BackingStoreException e) {
			mLogger.fatal("An exception occurred during printing of default preferences for plugin " + pluginName, e);
		}
	}

	/**
	 * Attaches Listener to all preferences and all scopes of all plugins to notify developers about changing
	 * preferences
	 *
	 * @param pluginId
	 */
	private void attachLogPreferenceChangeListenerToPlugin(final String pluginId, final String pluginName) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Attaching preference change listener for plugin " + pluginName);
		}
		final LogPreferenceChangeListener instanceListener = retrieveListener(pluginId, pluginName, "Instance");
		final LogPreferenceChangeListener configListener = retrieveListener(pluginId, pluginName, "Configuration");
		final LogPreferenceChangeListener defaultListener = retrieveListener(pluginId, pluginName, "Default");

		InstanceScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(instanceListener);
		InstanceScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(instanceListener);

		ConfigurationScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(configListener);
		ConfigurationScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(configListener);

		DefaultScope.INSTANCE.getNode(pluginId).removePreferenceChangeListener(defaultListener);
		DefaultScope.INSTANCE.getNode(pluginId).addPreferenceChangeListener(defaultListener);
	}

	private LogPreferenceChangeListener retrieveListener(final String pluginID, final String pluginName,
			final String scope) {
		final String listenerID = pluginID + scope;
		if (mActivePreferenceListener.containsKey(listenerID)) {
			return mActivePreferenceListener.get(listenerID);
		}
		final LogPreferenceChangeListener listener = new LogPreferenceChangeListener(scope, pluginID, pluginName);
		mActivePreferenceListener.put(listenerID, listener);
		return listener;
	}

	class LogPreferenceChangeListener implements IPreferenceChangeListener {

		private final String mScope;
		private final RcpPreferenceProvider mPreferences;
		private final String mPrefix;

		public LogPreferenceChangeListener(final String scope, final String pluginID, final String pluginName) {
			mScope = scope;
			mPreferences = new RcpPreferenceProvider(pluginID);
			mPrefix = "[" + pluginName + " (" + mScope + ")] Preference \"";
		}

		@Override
		public void preferenceChange(final PreferenceChangeEvent event) {
			mLogger.debug(mPrefix + event.getKey() + "\" changed: " + event.getOldValue() + " -> " + event.getNewValue()
					+ " (actual value in store: " + mPreferences.getString(event.getKey()) + ")");
		}
	}

}
