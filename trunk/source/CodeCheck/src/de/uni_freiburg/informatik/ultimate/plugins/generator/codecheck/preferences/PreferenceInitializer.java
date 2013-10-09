package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;



import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues;


/**
 * Provides default values for the preference page.
 * @see {@link AbstractPreferenceInitializer}{@link #initializeDefaultPreferences()}
 */

public class PreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		//obtain the default scope
		DefaultScope defaultscope = new DefaultScope();
//		IEclipsePreferences defaults = defaultscope.getNode(Activator.s_PLUGIN_ID);
		ScopedPreferenceStore preferences = new ScopedPreferenceStore(defaultscope,Activator.s_PLUGIN_ID);


		//set the default values
		preferences.setDefault(PreferenceValues.NAME_ONLYMAINPROCEDURE, 
				PreferenceValues.DEF_ONLYMAINPROCEDURE);
		preferences.setDefault(PreferenceValues.NAME_MEMOIZENORMALEDGECHECKS, 
				PreferenceValues.DEF_MEMOIZENORMALEDGECHECKS);
		preferences.setDefault(PreferenceValues.NAME_MEMOIZERETURNEDGECHECKS, 
				PreferenceValues.DEF_MEMOIZERETURNEDGECHECKS);
		
		preferences.setDefault(PreferenceValues.NAME_SOLVERANDINTERPOLATOR, 
				PreferenceValues.DEF_SOLVERANDINTERPOLATOR.toString());
		preferences.setDefault(PreferenceValues.NAME_INTERPOLATIONMODE,
				PreferenceValues.DEF_INTERPOLATIONMODE.toString());
		preferences.setDefault(PreferenceValues.NAME_PREDICATEUNIFICATION, 
				PreferenceValues.DEF_PREDICATEUNIFICATION.toString());
		preferences.setDefault(PreferenceValues.NAME_EDGECHECKOPTIMIZATION,
				PreferenceValues.DEF_EDGECHECKOPTIMIZATION.toString());
		
		preferences.setDefault(PreferenceValues.NAME_GRAPHWRITERPATH, PreferenceValues.DEF_GRAPHWRITERPATH);

	}

}