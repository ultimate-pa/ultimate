package de.uni_freiburg.informatik.ultimate.core.preferences;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
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

public class UltimatePreferenceStore {

	private final String mPluginID;

	private static HashMap<String, HashSet<IPreferenceChangeListener>> sActiveListener = new HashMap<String, HashSet<IPreferenceChangeListener>>();

	public UltimatePreferenceStore(String pluginID) {
		mPluginID = pluginID;
	}

	/*********************************** Getter ***********************************/

	/**
	 * Retrieves a preference value of type boolean from the store. If the key
	 * is neither in the current store nor in the default store, false is
	 * returned.
	 * 
	 * @param key
	 * @return
	 */
	public boolean getBoolean(String key) {
		return getBoolean(key, false);
	}

	public boolean getBoolean(String key, boolean defaultValue) {
		return getInstance().getBoolean(key, getDefault().getBoolean(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type String from the store. If the key is
	 * neither in the current store nor in the default store, "" is returned.
	 * 
	 * @param key
	 * @return
	 */
	public String getString(String key) {
		return getString(key, "");
	}

	public String getString(String key, String defaultValue) {
		return getInstance().get(key, getDefault().get(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type T, where T is a subtype of Enum,
	 * from the store. If the key is neither in the current store nor in the
	 * default store, an UnknownFormatConversionException is returned.
	 * 
	 * @param key
	 * @param enumType
	 * @return
	 * @throws UnknownFormatConversionException
	 */
	public <T extends Enum<T>> T getEnum(String key, Class<T> enumType) throws UnknownFormatConversionException {
		String strValue = getString(key);
		if (strValue.isEmpty()) {
			throw new UnknownFormatConversionException("String " + strValue + " cannot be converted to type "
					+ enumType);
		} else {
			return Enum.valueOf(enumType, strValue);
		}
	}

	/**
	 * Retrieves a preference value of type T, where T is a subtype of Enum,
	 * from the store. If the key is neither in the current store nor in the
	 * default store, defaultValue is returned.
	 * 
	 * @param key
	 * @param defaultValue
	 * @param enumType
	 * @return
	 */
	public <T extends Enum<T>> T getEnum(String key, T defaultValue, Class<T> enumType) {
		String strValue = getString(key);
		if (strValue.isEmpty()) {
			return defaultValue;
		} else {
			return Enum.valueOf(enumType, strValue);
		}
	}

	/**
	 * Retrieves a preference value of type byte[] from the store. If the key is
	 * neither in the current store nor in the default store, an empty byte
	 * array of length 0 is returned.
	 * 
	 * @param key
	 * @return
	 */
	public byte[] getByteArray(String key) {
		return getByteArray(key, new byte[0]);
	}

	public byte[] getByteArray(String key, byte[] defaultValue) {
		return getInstance().getByteArray(key, getDefault().getByteArray(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type double from the store. If the key is
	 * neither in the current store nor in the default store, 0.0d is returned.
	 * 
	 * @param key
	 * @return
	 */
	public double getDouble(String key) {
		return getDouble(key, 0.0d);
	}

	public double getDouble(String key, double defaultValue) {
		return getInstance().getDouble(key, getDefault().getDouble(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type float from the store. If the key is
	 * neither in the current store nor in the default store, 0.0f is returned.
	 * 
	 * @param key
	 * @return
	 */
	public float getFloat(String key) {
		return getFloat(key, 0.0f);
	}

	public float getFloat(String key, float defaultValue) {
		return getInstance().getFloat(key, getDefault().getFloat(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type int from the store. If the key is
	 * neither in the current store nor in the default store, 0 is returned.
	 * 
	 * @param key
	 * @return
	 */
	public int getInt(String key) {
		return getInt(key, 0);
	}

	public int getInt(String key, int defaultValue) {
		return getInstance().getInt(key, getDefault().getInt(key, defaultValue));
	}

	/**
	 * Retrieves a preference value of type long from the store. If the key is
	 * neither in the current store nor in the default store, 0L is returned.
	 * 
	 * @param key
	 * @return
	 */
	public long getLong(String key) {
		return getLong(key, 0L);
	}

	public long getLong(String key, long defaultValue) {
		return getInstance().getLong(key, getDefault().getLong(key, defaultValue));
	}

	/*********************************** End Getter ***********************************/

	/*********************************** Setter ***********************************/

	public void put(String key, String value) {
		getInstance().put(key, value);
		try {
			getInstance().flush();
		} catch (BackingStoreException e) {
			e.printStackTrace();
		}
	}

	/*********************************** End Setter ***********************************/

	public void addPreferenceChangeListener(IPreferenceChangeListener iPreferenceChangeListener) {
		addPreferenceChangeListener(mPluginID, iPreferenceChangeListener);

	}

	private static void addPreferenceChangeListener(String id, IPreferenceChangeListener iPreferenceChangeListener) {
		InstanceScope.INSTANCE.getNode(id).addPreferenceChangeListener(iPreferenceChangeListener);

		if (sActiveListener.containsKey(id)) {
			sActiveListener.get(id).add(iPreferenceChangeListener);
		} else {
			HashSet<IPreferenceChangeListener> list = new HashSet<IPreferenceChangeListener>();
			list.add(iPreferenceChangeListener);
			sActiveListener.put(id, list);
		}
	}

	public void removePreferenceChangeListener(IPreferenceChangeListener iPreferenceChangeListener) {
		getInstance().removePreferenceChangeListener(iPreferenceChangeListener);
		if (sActiveListener.containsKey(mPluginID)) {
			sActiveListener.get(mPluginID).remove(iPreferenceChangeListener);
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

	public void exportPreferences(OutputStream outputStream) throws CoreException {
		Platform.getPreferencesService().exportPreferences(getInstance(), outputStream, null);
	}

	public static IStatus importPreferences(InputStream inputStream) throws CoreException {

		IStatus status = Platform.getPreferencesService().importPreferences(inputStream);
		if (status.isOK()) {
			for (Entry<String, HashSet<IPreferenceChangeListener>> entry : sActiveListener.entrySet()) {
				for (IPreferenceChangeListener listener : entry.getValue()) {
					InstanceScope.INSTANCE.getNode(entry.getKey()).removePreferenceChangeListener(listener);
					addPreferenceChangeListener(entry.getKey(), listener);
				}
			}

		}
		return status;
	}

	public String getDefaultPreferencesString() {
		StringBuilder sb = new StringBuilder();
		try {
			for (String key : getDefault().keys()) {
				sb.append(key).append("=").append(getDefault().get(key, "NO DEFAULT SET")).append("\n");
			}
		} catch (BackingStoreException e) {
			e.printStackTrace();
			return "";
		}
		return sb.toString();
	}

	public String getCurrentPreferencesString() {
		StringBuilder sb = new StringBuilder();
		try {
			for (String key : getDefault().keys()) {
				sb.append(key).append("=").append(getString(key, "NO DEFAULT SET")).append("\n");
			}
		} catch (BackingStoreException e) {
			e.printStackTrace();
			return "";
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

}
