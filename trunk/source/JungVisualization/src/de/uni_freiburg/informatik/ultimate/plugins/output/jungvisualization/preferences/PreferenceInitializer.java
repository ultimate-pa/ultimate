package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * Provides default values for the preference page.
 * @see {@link AbstractPreferenceInitializer}{@link #initializeDefaultPreferences()}
 * 
 * @author lena 
 *
 */

public class PreferenceInitializer extends AbstractPreferenceInitializer {

	@Override
	public void initializeDefaultPreferences() {
		//obtain the default scope
		DefaultScope defaultscope = new DefaultScope();
		IEclipsePreferences defaults = defaultscope.getNode(Activator.PLUGIN_ID);
		ScopedPreferenceStore store = new ScopedPreferenceStore(defaultscope,Activator.PLUGIN_ID);
		
		//set the default values
		defaults.put(PreferenceValues.NAME_PATH, PreferenceValues.VALUE_PATH_DEFAULT);
		defaults.putBoolean(PreferenceValues.NAME_ANNOTATED_EDGES, PreferenceValues.VALUE_ANNOTATED_EDGES_DEFAULT);
		defaults.putBoolean(PreferenceValues.NAME_ANNOTATED_NODES, PreferenceValues.VALUE_ANNOTATED_NODES_DEFAULT);
		defaults.put(PreferenceValues.NAME_LAYOUT, PreferenceValues.VALUE_LAYOUT_DEFAULT);
		defaults.put(PreferenceValues.NAME_SHAPE_NODE, PreferenceValues.VALUE_SHAPE_NODE_DEFAULT);
		PreferenceConverter.setValue(store, PreferenceValues.NAME_COLOR_BACKGROUND, PreferenceValues.VALUE_COLOR_BACKGROUND_DEFAULT);
		PreferenceConverter.setValue(store, PreferenceValues.NAME_COLOR_NODE, PreferenceValues.VALUE_COLOR_NODE_DEFAULT);
		PreferenceConverter.setValue(store, PreferenceValues.NAME_COLOR_NODE_PICKED, PreferenceValues.VALUE_COLOR_NODE_PICKED_DEFAULT);

	}

}
