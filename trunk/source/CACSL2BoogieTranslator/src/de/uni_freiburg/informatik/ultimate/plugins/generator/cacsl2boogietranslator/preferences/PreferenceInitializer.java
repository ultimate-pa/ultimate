package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<TranslationMode>(LABEL_MODE,
						TranslationMode.BASE, PreferenceType.Radio,
						TranslationMode.values()),
				new UltimatePreferenceItem<String>(LABEL_MAINPROC, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_POINTER_VALIDITY, false,
						PreferenceType.Boolean), };
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "C+ACSL to Boogie Translator";
	}

	public static final String LABEL_MODE = "Translation Mode:";
	public static final String LABEL_MAINPROC = "Checked method. Library mode if empty.";
	public static final String LABEL_CHECK_POINTER_VALIDITY = "Check if pointer is valid before each access";

}
