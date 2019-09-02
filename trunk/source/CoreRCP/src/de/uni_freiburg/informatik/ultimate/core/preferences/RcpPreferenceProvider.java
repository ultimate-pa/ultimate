/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.core.preferences;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.UnknownFormatConversionException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.PreferenceException;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RcpPreferenceProvider implements IPreferenceProvider {

	private final String mPluginID;
	private static final Map<String, Set<IPreferenceChangeListener>> ACTIVE_LISTENER = new HashMap<>();

	public RcpPreferenceProvider(final String pluginID) {
		mPluginID = pluginID;
	}

	/**
	 * Retrieves a preference value of type boolean from the store. If the key is neither in the current store nor in
	 * the default store, false is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public boolean getBoolean(final String key) {
		return getBoolean(key, false);
	}

	@Override
	public boolean getBoolean(final String key, final boolean defaultValue) {
		return getInstance().getBoolean(key, getDefault().getBoolean(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type String from the store. If the key is neither in the current store nor in the
	 * default store, "" is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public String getString(final String key) {
		return getString(key, "");
	}

	@Override
	public String getString(final String key, final String defaultValue) {
		return getInstance().get(key, getDefault().get(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type T, where T is a subtype of Enum, from the store. If the key is neither in
	 * the current store nor in the default store, an UnknownFormatConversionException is returned.
	 *
	 * @param key
	 * @param enumType
	 * @return
	 */
	@Override
	public <T extends Enum<T>> T getEnum(final String key, final Class<T> enumType) {
		final String strValue = getString(key);
		if (strValue.isEmpty()) {
			throw new UnknownFormatConversionException("An empty string cannot be converted to type " + enumType);
		}
		return Enum.valueOf(enumType, strValue);
	}

	/**
	 * Retrieves a preference value of type T, where T is a subtype of Enum, from the store. If the key is neither in
	 * the current store nor in the default store, defaultValue is returned.
	 *
	 * @param key
	 * @param defaultValue
	 * @param enumType
	 * @return
	 */
	@Override
	public <T extends Enum<T>> T getEnum(final String key, final T defaultValue, final Class<T> enumType) {
		final String strValue = getString(key);
		if (strValue.isEmpty()) {
			return defaultValue;
		}
		return Enum.valueOf(enumType, strValue);
	}

	/**
	 * Retrieves a preference value of type byte[] from the store. If the key is neither in the current store nor in the
	 * default store, an empty byte array of length 0 is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public byte[] getByteArray(final String key) {
		return getByteArray(key, new byte[0]);
	}

	@Override
	public byte[] getByteArray(final String key, final byte[] defaultValue) {
		return getInstance().getByteArray(key, getDefault().getByteArray(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type double from the store. If the key is neither in the current store nor in the
	 * default store, 0.0d is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public double getDouble(final String key) {
		return getDouble(key, 0.0D);
	}

	@Override
	public double getDouble(final String key, final double defaultValue) {
		return getInstance().getDouble(key, getDefault().getDouble(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type float from the store. If the key is neither in the current store nor in the
	 * default store, 0.0f is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public float getFloat(final String key) {
		return getFloat(key, 0.0F);
	}

	@Override
	public float getFloat(final String key, final float defaultValue) {
		return getInstance().getFloat(key, getDefault().getFloat(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type int from the store. If the key is neither in the current store nor in the
	 * default store, 0 is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public int getInt(final String key) {
		return getInt(key, 0);
	}

	@Override
	public int getInt(final String key, final int defaultValue) {
		return getInstance().getInt(key, getDefault().getInt(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type long from the store. If the key is neither in the current store nor in the
	 * default store, 0L is returned.
	 *
	 * @param key
	 * @return
	 */
	@Override
	public long getLong(final String key) {
		return getLong(key, 0L);
	}

	@Override
	public long getLong(final String key, final long defaultValue) {
		return getInstance().getLong(key, getDefault().getLong(key, defaultValue));
	}

	@Override
	public void put(final String key, final String value) {
		getInstance().put(key, value);
		try {
			getInstance().flush();
		} catch (final BackingStoreException e) {
			throw new PreferenceException(mPluginID, e);
		}
	}

	public void addPreferenceChangeListener(final IPreferenceChangeListener preferenceChangeListener) {
		addPreferenceChangeListener(mPluginID, preferenceChangeListener);
	}

	private static void addPreferenceChangeListener(final String id,
			final IPreferenceChangeListener iPreferenceChangeListener) {
		InstanceScope.INSTANCE.getNode(id).addPreferenceChangeListener(iPreferenceChangeListener);

		Set<IPreferenceChangeListener> set = ACTIVE_LISTENER.get(id);
		if (set == null) {
			set = new HashSet<>();
			ACTIVE_LISTENER.put(id, set);
		}
		set.add(iPreferenceChangeListener);
	}

	public void removePreferenceChangeListener(final IPreferenceChangeListener iPreferenceChangeListener) {
		getInstance().removePreferenceChangeListener(iPreferenceChangeListener);
		if (ACTIVE_LISTENER.containsKey(mPluginID)) {
			ACTIVE_LISTENER.get(mPluginID).remove(iPreferenceChangeListener);
		}
	}

	public IEclipsePreferences getDefaultEclipsePreferences() {
		return getDefault();
	}

	public IEclipsePreferences getEclipsePreferences() {
		return getInstance();
	}

	public IScopeContext getScopeContext() {
		return InstanceScope.INSTANCE;
	}

	public void exportPreferences(final OutputStream outputStream) throws CoreException {
		Platform.getPreferencesService().exportPreferences(getInstance(), outputStream, null);
	}

	public static IStatus importPreferences(final InputStream inputStream) throws CoreException {
		final IStatus status = Platform.getPreferencesService().importPreferences(inputStream);
		if (status.isOK()) {
			for (final Entry<String, Set<IPreferenceChangeListener>> entry : ACTIVE_LISTENER.entrySet()) {
				for (final IPreferenceChangeListener listener : entry.getValue()) {
					InstanceScope.INSTANCE.getNode(entry.getKey()).removePreferenceChangeListener(listener);
					addPreferenceChangeListener(entry.getKey(), listener);
				}
			}

		}
		return status;
	}

	/**
	 * Get an array of strings were each entry represents all preferences that differ from their default values.
	 */
	public String[] getDeltaPreferencesStrings() {
		final List<String> rtr = new ArrayList<>();
		final String fallback = "NO DEFAULT SET";
		try {
			final IEclipsePreferences defaults = getDefault();
			final IEclipsePreferences instance = getInstance();
			for (final String defaultKey : defaults.keys()) {
				final String defaultValue = defaults.get(defaultKey, fallback);
				final String currentValue = instance.get(defaultKey, defaultValue);
				if (!currentValue.equals(defaultValue)) {
					rtr.add(defaultKey + "=" + currentValue);
				}
			}
		} catch (final BackingStoreException e) {
			throw new PreferenceException(mPluginID, e);
		}

		return rtr.toArray(new String[rtr.size()]);
	}

	/**
	 * @return A map from key to value of the default preferences for this provider
	 */
	public Map<String, Object> getDefaultPreferences() {
		final Map<String, Object> rtr = new HashMap<>();
		try {
			final IEclipsePreferences defaults = getDefault();
			for (final String defaultKey : defaults.keys()) {
				final Object defaultValue = defaults.get(defaultKey, null);
				rtr.put(defaultKey, defaultValue);
			}
		} catch (final BackingStoreException e) {
			throw new PreferenceException(mPluginID, e);
		}
		return rtr;
	}

	@Override
	public String getSingleLinePreferenceString() {
		final StringBuilder sb = new StringBuilder();
		try {
			final IEclipsePreferences instancePrefs = getInstance();
			final IEclipsePreferences defaultPrefs = getDefault();
			final String delim = " ♦ ";
			for (final String prefKey : defaultPrefs.keys()) {
				final Object activeValue = instancePrefs.get(prefKey, defaultPrefs.get(prefKey, null));
				sb.append(prefKey).append('=').append(activeValue).append(delim);
			}
			sb.setLength(Math.max(0, sb.length() - delim.length()));
		} catch (final BackingStoreException e) {
			throw new PreferenceException(mPluginID, e);
		}
		return sb.toString();
	}

	@Override
	public String toString() {
		return mPluginID + " UltimatePreferenceStore";
	}

	private IEclipsePreferences getInstance() {
		return InstanceScope.INSTANCE.getNode(mPluginID);
	}

	private IEclipsePreferences getDefault() {
		return DefaultScope.INSTANCE.getNode(mPluginID);
	}

	@Override
	public void put(final String key, final Object value) {
		if (value == null) {
			put(key, (String) null);
		} else {
			put(key, value.toString());
		}
	}

}
