package de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction.Activator;

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
		store.setDefault(PreferenceConstants.P_MEMOIZE, true);
		store.setDefault(PreferenceConstants.P_ANNOTATE_EDGES, true);
		store.setDefault(PreferenceConstants.P_ANNOTATE_NODES, true);
		store.setDefault(PreferenceConstants.P_SHOW_UNREACHABLE, true);
//		store.setDefault(PreferenceConstants.P_BOOLEAN, true);
//		store.setDefault(PreferenceConstants.P_CHOICE, "choice2");
//		store.setDefault(PreferenceConstants.P_STRING,
//				"Default value");
	}

}
