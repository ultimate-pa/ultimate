package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;



import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;


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
		ScopedPreferenceStore preferences = new ScopedPreferenceStore(defaultscope,Activator.PLUGIN_ID);


		//set the default values
		preferences.setDefault(PreferenceValues.NAME_INTERPROCEDUTAL, PreferenceValues.DEF_INTERPROCEDUTAL);
		preferences.setDefault(PreferenceValues.NAME_AllErrorsAtOnce, PreferenceValues.DEF_AllErrorsAtOnce);
		preferences.setDefault(PreferenceValues.NAME_LETTER, PreferenceValues.DEF_LETTER);
		preferences.setDefault(PreferenceValues.NAME_SOLVER, PreferenceValues.DEF_SOLVER.toString());
		preferences.setDefault(PreferenceValues.NAME_TIMEOUT, PreferenceValues.DEF_TIMEOUT);
		preferences.setDefault(PreferenceValues.NAME_ITERATIONS, PreferenceValues.DEF_ITERATIONS);
		preferences.setDefault(PreferenceValues.NAME_HOARE, PreferenceValues.DEF_HOARE);
		preferences.setDefault(PreferenceValues.NAME_ARTIFACT, PreferenceValues.DEF_ARTIFACT);
		preferences.setDefault(PreferenceValues.NAME_WATCHITERATION, PreferenceValues.DEF_WATCHITERATION);
		preferences.setDefault(PreferenceValues.NAME_INTERPOLATED_LOCS, PreferenceValues.DEF_INTERPOLANTS.toString());
		preferences.setDefault(PreferenceValues.NAME_EDGES2TRUE, PreferenceValues.DEF_EDGES2TRUE);
		preferences.setDefault(PreferenceValues.NAME_InterpolantAutomaton, PreferenceValues.DEF_ADDITIONAL_EDGES);
		preferences.setDefault(PreferenceValues.NAME_DUMPSCRIPT, PreferenceValues.DEF_DUMPSCRIPT);
		preferences.setDefault(PreferenceValues.NAME_DUMPFORMULAS, PreferenceValues.DEF_DUMPFORMULAS);
		preferences.setDefault(PreferenceValues.NAME_DUMPAUTOMATA, PreferenceValues.DEF_DUMPAUTOMATA);		
		preferences.setDefault(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);
		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		preferences.setDefault(PreferenceValues.NAME_DIFFERENCE_SENWA, PreferenceValues.DEF_DIFFERENCE_SENWA);
		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		preferences.setDefault(PreferenceValues.NAME_MINIMIZE, PreferenceValues.DEF_MINIMIZE);
		preferences.setDefault(PreferenceValues.NAME_CONCURRENCY, PreferenceValues.DEF_CONCURRENCY);
		preferences.setDefault(PreferenceValues.NAME_MAINPROC, "");
		preferences.setDefault(PreferenceValues.NAME_Order, PreferenceValues.DEF_Order);
		preferences.setDefault(PreferenceValues.NAME_cutOff, PreferenceValues.DEF_cutOff);
		preferences.setDefault(PreferenceValues.NAME_unfolding2Net, PreferenceValues.DEF_unfolding2Net);
		preferences.setDefault(PreferenceValues.NAME_simplifyCodeBlocks, PreferenceValues.DEF_simplifyCodeBlocks);
		preferences.setDefault(PreferenceValues.NAME_PreserveGotoEdges, PreferenceValues.DEF_PreserveGotoEdges);
	}

}