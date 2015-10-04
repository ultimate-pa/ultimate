package de.uni_freiburg.informatik.ultimate.source.java.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.source.java.Activator;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Java2BoogiePreferenceInitializer extends UltimatePreferenceInitializer {

	public enum Mode {
		Soot2Cfg, Joogie
	}

	private static final String PREFERENCE_MODE = "Mode";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {
				new UltimatePreferenceItem<Mode>(PREFERENCE_MODE, Mode.Joogie, PreferenceType.Combo, Mode.values()), };
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}

	public static Mode getMode() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(PREFERENCE_MODE, Mode.class);
	}

}
