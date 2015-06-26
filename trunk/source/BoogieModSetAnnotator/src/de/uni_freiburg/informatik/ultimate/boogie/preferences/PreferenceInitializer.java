package de.uni_freiburg.informatik.ultimate.boogie.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.modsetannotator.Activator;

/**
 * 
 * This class loads preference default values before they are needed
 * 
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the
 * plugin.xml
 * 
 * @author dietsch
 * 
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {

		return new UltimatePreferenceItem<?>[] { new UltimatePreferenceItem<Boolean>(
				LABEL_SHOWALLANNOTATIONS, false, PreferenceType.Boolean) };
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Boogie Modset Annotator";
	}

	public static final String LABEL_SHOWALLANNOTATIONS = "Show all Annotations";

}
