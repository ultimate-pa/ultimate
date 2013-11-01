package de.uni_freiburg.informatik.ultimate.core.preferences;

import java.io.InputStream;
import java.io.OutputStream;

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

	// private Logger mLogger;
	private final String mPluginID;

	private final IEclipsePreferences mCurrentPreferences;
	private final IEclipsePreferences mDefaultPreferences;

	public UltimatePreferenceStore(String pluginID) {
		mPluginID = pluginID;
		mCurrentPreferences = InstanceScope.INSTANCE.getNode(mPluginID);
		mDefaultPreferences = DefaultScope.INSTANCE.getNode(mPluginID);
	}

	public void addPreferenceChangeListener(
			IPreferenceChangeListener iPreferenceChangeListener) {
		mCurrentPreferences
				.addPreferenceChangeListener(iPreferenceChangeListener);
	}

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
		return mCurrentPreferences.getBoolean(key,
				mDefaultPreferences.getBoolean(key, defaultValue));
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
		return mCurrentPreferences.get(key,
				mDefaultPreferences.get(key, defaultValue));
	}

	public IEclipsePreferences getDefaultEclipsePreferences() {
		return mDefaultPreferences;
	}

	public IEclipsePreferences getEclipsePreferences() {
		return mCurrentPreferences;
	}

	public String getDefaultPreferencesString() {
		StringBuilder sb = new StringBuilder();
		try {
			for (String key : mDefaultPreferences.keys()) {
				sb.append(key).append("=")
						.append(mDefaultPreferences.get(key, "NO DEFAULT SET"))
						.append("\n");
			}
		} catch (BackingStoreException e) {
			e.printStackTrace();
			return e.getMessage();
		}
		return sb.toString();
	}

	public IScopeContext getScopeContext() {
		return InstanceScope.INSTANCE;
	}

	public void exportPreferences(OutputStream outputStream)
			throws CoreException {
		Platform.getPreferencesService().exportPreferences(mCurrentPreferences,
				outputStream,null);
	}

	public static IStatus importPreferences(InputStream inputStream)
			throws CoreException {
		return Platform.getPreferencesService().importPreferences(inputStream);
	}

}
