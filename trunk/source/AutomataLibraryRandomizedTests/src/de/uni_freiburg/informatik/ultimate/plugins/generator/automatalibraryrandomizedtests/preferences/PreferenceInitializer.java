package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;


import de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.Activator;

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
		store.setDefault(PreferenceConstants.Name_Operation, PreferenceConstants.Default_Operation);
		store.setDefault(PreferenceConstants.Name_NumberOfLetters, PreferenceConstants.Default_NumberOfLetters);
		store.setDefault(PreferenceConstants.Name_NumberOfStates, PreferenceConstants.Default_NumberOfStates);
		store.setDefault(PreferenceConstants.Name_ProbabilityInitial, PreferenceConstants.Default_ProbabilityInitial);
		store.setDefault(PreferenceConstants.Name_ProbabilityFinal, PreferenceConstants.Default_ProbabilityFinal);
		store.setDefault(PreferenceConstants.Name_ProbabilityInternalTransition, PreferenceConstants.Default_ProbabilityInternalTransition);
		store.setDefault(PreferenceConstants.Name_ProbabilityCallTransition, PreferenceConstants.Default_ProbabilityCallTransition);
		store.setDefault(PreferenceConstants.Name_ProbabilityReturnTransition, PreferenceConstants.Default_ProbabilityReturnTransition);
	}

}
