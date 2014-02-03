package de.uni_freiburg.informatik.ultimate.irsdependencies.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;

/**
 * @author Dietsch
 * 
 */
public class IRSDependenciesPreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {
				new UltimatePreferenceItem<Boolean>(Mode,
						false, PreferenceType.Boolean),
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return getPlugID();
	}

	
	public static final String Mode = "Mode";
	

}
