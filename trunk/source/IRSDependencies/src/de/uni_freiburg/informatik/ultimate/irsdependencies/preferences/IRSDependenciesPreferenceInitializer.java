package de.uni_freiburg.informatik.ultimate.irsdependencies.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
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
				new UltimatePreferenceItem<Mode>(sMode,
						Mode.Default, PreferenceType.Combo,Mode.values()),
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

	
	private static final String sMode = "Mode";
	
	public enum Mode{
		Default
	}
	
	
	public static Mode getMode(){
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(sMode, Mode.class);
	}

}
