package local.stalin.boogie.DSITransformer.preferences;

import local.stalin.boogie.DSITransformer.Activator;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

/**
 * 
 * This class loads preference default values before they are needed
 * 
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the
 * plugin.xml
 * 
 * @author various
 * 
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	// @Override
	public void initializeDefaultPreferences() {
		IEclipsePreferences defaults = new DefaultScope()
				.getNode(Activator.s_PLUGIN_ID);

		defaults.putBoolean(PreferenceValues.NAME_ALLFUNCTIONS,
				PreferenceValues.VALUE_ALLFUNCTIONS_DEFAULT);

		defaults.putBoolean(PreferenceValues.NAME_TRIMWRAP,
				PreferenceValues.VALUE_TRIMWRAP_DEFAULT);

		defaults.putBoolean(PreferenceValues.NAME_LEAVEPROCEDURES,
				PreferenceValues.VALUE_LEAVEPROCEDURES);
	}

}
