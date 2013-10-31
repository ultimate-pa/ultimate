package de.uni_freiburg.informatik.ultimate.core.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.osgi.service.prefs.BackingStoreException;

/**
 * UltimatePreferenceInitializer implements an AbstractPreferenceInitializer for
 * Ultimate. It initializes the default values for preferences and provides
 * access to the preferences for Ultimate.
 * 
 * Clients should derive from this class and contribute to the extension point
 * org.eclipse.core.runtime.preferences.initializer (see the plugin.xml of
 * CoreRCP for an example)
 * 
 * @author Dietsch
 * 
 */
public abstract class UltimatePreferenceInitializer extends
		AbstractPreferenceInitializer {

	private final UltimatePreferenceItem[] mPreferenceDescriptors;
	private final UltimatePreferenceStore mPreferenceStore;

	public UltimatePreferenceInitializer() {
		mPreferenceDescriptors = initDefaultPreferences();
		mPreferenceStore = new UltimatePreferenceStore(getPlugID());
	}

	/***
	 * This method is called by the preference initializer to initialize default
	 * preference values.
	 * 
	 * Note: Clients should not call this method. It will be called
	 * automatically by the preference initializer when the appropriate default
	 * preference node is accessed.
	 */
	@Override
	public void initializeDefaultPreferences() {
		IEclipsePreferences defaults = mPreferenceStore
				.getDefaultEclipsePreferences();

		for (UltimatePreferenceItem item : mPreferenceDescriptors) {
			switch (item.getType()) {
			case Boolean:
				defaults.putBoolean(item.getLabel(),
						(Boolean) item.getDefaultValue());
				break;
			case Directory:
			case String:
				defaults.put(item.getLabel(), (String) item.getDefaultValue());
				break;
			case Label:
				// A Label is not really a preference; its just nice for
				// automatic generation of preference pages
				break;
			default:
				throw new UnsupportedOperationException(
						"You need to implement the new enum type \""
								+ item.getType() + "\" here");
			}

		}
		try {
			defaults.sync();
		} catch (BackingStoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// FIXME: For debug purposes
		// System.out.println(mPreferenceStore.getDefaultPreferencesString());

	}

	public UltimatePreferenceItem[] getDefaultPreferences() {
		return mPreferenceDescriptors;
	}

	/**
	 * Should return an array of UltimatePreferenceItem describing the
	 * preferences of the implementing plugin. Will be called once during
	 * construction.
	 * 
	 * The index prescribes the position in preference pages.
	 * 
	 * Note: Clients should only set default preference values for their own
	 * plugin.
	 * 
	 * @return
	 */
	protected abstract UltimatePreferenceItem[] initDefaultPreferences();

	/**
	 * Should return the ID of the implementing plugin.
	 * 
	 * @return
	 */
	protected abstract String getPlugID();

}
