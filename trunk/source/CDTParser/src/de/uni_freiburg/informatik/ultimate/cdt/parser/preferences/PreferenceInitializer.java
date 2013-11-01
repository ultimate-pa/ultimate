package de.uni_freiburg.informatik.ultimate.cdt.parser.preferences;


import de.uni_freiburg.informatik.ultimate.cdt.parser.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[]{
				new UltimatePreferenceItem<String>(INCLUDE_PATHS, "", PreferenceType.Path)
		};
	}

	
	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "CDT Parser";
	}
	
	public static final String INCLUDE_PATHS = "Please specify include paths that will be parsed with the given C-File";

}
