/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.core.preferences;

import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.PreferenceException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RcpPreferenceBinder {

	private RcpPreferenceBinder() {
		// do not construct utility class
	}

	/**
	 * Initialize an RCP-based backing store with preferences stored in {@link BaseUltimatePreferenceItem}s.
	 * 
	 * @param preferenceStore
	 *            The preference store in which you want to save your preferences.
	 * @param preferenceDescriptors
	 *            The preference items you want to use as source.
	 */
	public static void initializePreferences(final IEclipsePreferences preferenceStore,
			final BaseUltimatePreferenceItem[] preferenceDescriptors) {
		flushEclipsePreferences(preferenceStore);

		for (final BaseUltimatePreferenceItem prefItem : BaseUltimatePreferenceItem
				.constructFlattenedList(preferenceDescriptors)) {
			if (prefItem instanceof UltimatePreferenceItem) {
				final UltimatePreferenceItem<?> item = (UltimatePreferenceItem<?>) prefItem;
				final String label = item.getLabel();
				final Object value = item.getDefaultValue();
				preferenceStore.remove(label);

				switch (item.getType()) {
				case Boolean:
					preferenceStore.putBoolean(label, (Boolean) value);
					break;
				case Integer:
					preferenceStore.putInt(label, (Integer) value);
					break;
				case Directory:
				case String:
				case MultilineString:
				case Combo:
				case Radio:
				case Path:
				case File:
				case Color:
					preferenceStore.put(label, value.toString());
					break;
				case Label:
					// A Label is not really a preference; its just nice for
					// automatic generation of preference pages
					break;
				default:
					throw new IllegalArgumentException(
							"You need to implement the new enum type \"" + item.getType() + "\" here");
				}
			}
		}
		flushEclipsePreferences(preferenceStore);
	}

	/**
	 * Get the RCP backing store for storing the current values of preferences for a given plugin.
	 * 
	 * @param pluginId
	 *            The id of the given plugin.
	 * @return A RCP backing store.
	 */
	public static IEclipsePreferences getInstanceStore(final String pluginId) {
		return InstanceScope.INSTANCE.getNode(pluginId);
	}

	/**
	 * Get the RCP backing store for storing default values of preferences for a given plugin.
	 * 
	 * @param pluginId
	 *            The id of the given plugin.
	 * @return A RCP backing store.
	 */
	public static IEclipsePreferences getDefaultStore(final String pluginId) {
		return DefaultScope.INSTANCE.getNode(pluginId);
	}

	/**
	 * Reset the intersection of all registered preferences with the specified preferences for the specified plugin to
	 * their default values.
	 * 
	 * @param pluginId
	 *            The identifier of the plugin for which preferences should be reseted to default values.
	 * @param preferenceDescriptors
	 *            The preferences that should be reseted if they are registered.
	 */
	public static void resetToDefaultPreferences(final String pluginId,
			final BaseUltimatePreferenceItem[] preferenceDescriptors) {
		final IEclipsePreferences instanceStore = getInstanceStore(pluginId);
		initializePreferences(instanceStore, preferenceDescriptors);
	}

	/**
	 * Register preferences and set their values to the default values.
	 * 
	 * @param pluginId
	 *            The plugin for which preferences should be registered.
	 * @param preferenceDescriptors
	 *            The preferences and their initial values.
	 */
	public static void registerDefaultPreferences(final String pluginId,
			final BaseUltimatePreferenceItem[] preferenceDescriptors) {
		final IEclipsePreferences instanceStore = getDefaultStore(pluginId);
		initializePreferences(instanceStore, preferenceDescriptors);
	}

	private static void flushEclipsePreferences(final IEclipsePreferences prefs) {
		try {
			prefs.flush();
			prefs.sync();
		} catch (final BackingStoreException e) {
			throw new PreferenceException(Activator.PLUGIN_ID, e);
		}
	}
}
