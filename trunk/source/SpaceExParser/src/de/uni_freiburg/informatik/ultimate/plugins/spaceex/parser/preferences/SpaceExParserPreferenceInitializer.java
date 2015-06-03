package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator;

/**
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SpaceExParserPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum Mode {
		Default
	}

	private static final String sMode = "Mode";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] { new UltimatePreferenceItem<Mode>(sMode, Mode.Default,
				PreferenceType.Combo, Mode.values()), };
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
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(sMode, Mode.class);
	}

}
