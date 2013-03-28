package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;


import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.Activator;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
		store.setDefault(PreferenceConstants.Name_WriteToFile, PreferenceConstants.Default_WriteToFile);
		store.setDefault(PreferenceConstants.Name_Path, PreferenceConstants.Default_Path);
		store.setDefault(PreferenceConstants.Name_Timeout, PreferenceConstants.Default_Timeout);
	}

}
