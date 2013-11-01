package de.uni_freiburg.informatik.ultimate.automata.preferences;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(Name_Write, Default_Write,PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(Name_Path, Default_Path, PreferenceType.Directory)
		};
	}
	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}
	@Override
	public String getPreferencePageTitle() {
		return "Nested Word Automata Library";
	}
	
	public static final String Name_Path = "Write files in directory:";
	public static final String Name_Write = "Write failed operation checks to files";

	public static final String Default_Path = ".";
	public static final boolean Default_Write = false;
}
