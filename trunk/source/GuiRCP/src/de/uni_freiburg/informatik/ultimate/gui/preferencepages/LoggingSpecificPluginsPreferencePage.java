/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.Arrays;
import java.util.StringTokenizer;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;

public class LoggingSpecificPluginsPreferencePage extends AbstractDetailsPreferencePage {

	private final ScopedPreferenceStore mPreferenceStore;

	public LoggingSpecificPluginsPreferencePage() {
		mPreferenceStore = new ScopedPreferenceStore(InstanceScope.INSTANCE, CorePreferenceInitializer.PLUGINID);
	}

	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return mPreferenceStore;
	}

	@Override
	protected String[] getDefaults() {
		return convert(mPreferenceStore.getDefaultString(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC));
	}

	@Override
	protected String getInvalidEntryMessage() {
		return CorePreferenceInitializer.INVALID_ENTRY;
	}

	@Override
	protected String[] getPreferenceAsStringArray() {
		return convert(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC));
	}

	@Override
	protected void setThePreference(final String[] items) {
		final StringBuilder buffer = new StringBuilder();
		for (int i = 0; i < items.length; i++) {
			buffer.append(items[i]);
			buffer.append(CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		}
		mPreferenceStore.setValue(CorePreferenceInitializer.LABEL_LOGLEVEL_PLUGIN_SPECIFIC, buffer.toString());
	}

	@Override
	protected String getInfoContent(final List detailList) {
		final StringBuilder invalidPluginIds = new StringBuilder();
		invalidPluginIds.append(CorePreferenceInitializer.PLUGINS_NOT_PRESENT);
		boolean error = false;
		for (final String line : detailList.getItems()) {
			final String pluginId = line.substring(0, line.lastIndexOf('='));
			if (!isActivePluginId(pluginId)) {
				error = true;
				invalidPluginIds.append(pluginId + "\n");
			}
		}
		if (error) {
			return invalidPluginIds.toString();
		}
		return CorePreferenceInitializer.ALL_PLUGINS_PRESENT;
	}

	private static boolean isActivePluginId(final String pluginId) {
		// hack until this class is auto-generated
		final String[] plugins = UltimateCore.getPluginNames();
		boolean retVal = false;
		for (final String iTool : plugins) {
			if (iTool.equals(pluginId)) {
				retVal = true;
			}
		}
		return retVal;
	}

	@Override
	protected String[] getComboSupply() {
		// hack until this class is auto-generated
		final String[] plugins = UltimateCore.getPluginNames();

		if (plugins == null) {
			return new String[0];
		}
		Arrays.sort(plugins);
		final String[] rtr = new String[plugins.length];
		for (int i = 0; i < plugins.length; i++) {
			rtr[i] = plugins[i] + "=<LOG LEVEL>";
		}
		return rtr;
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
}
