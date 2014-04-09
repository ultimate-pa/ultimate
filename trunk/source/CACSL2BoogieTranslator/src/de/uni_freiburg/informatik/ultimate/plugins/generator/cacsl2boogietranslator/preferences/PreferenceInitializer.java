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
				new UltimatePreferenceItem<POINTER_BASE_VALIDITY>(
						LABEL_CHECK_POINTER_VALIDITY, 
							POINTER_BASE_VALIDITY.ASSERTandASSUME,
							PreferenceType.Combo, POINTER_BASE_VALIDITY.values()),
				new UltimatePreferenceItem<POINTER_ALLOCATED>(
							LABEL_CHECK_POINTER_ALLOC, 
							POINTER_ALLOCATED.ASSERTandASSUME,
							PreferenceType.Combo, POINTER_ALLOCATED.values()),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_FREE_VALID, true,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_MemoryLeakInMain, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_CHECK_MallocNonNegative, false,
						PreferenceType.Boolean), 
				new UltimatePreferenceItem<Boolean>(
						LABEL_REPORT_UNSOUNDNESS_WARNING, false,
						PreferenceType.Boolean) 
		};
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
	public static final String LABEL_CHECK_POINTER_VALIDITY = "Pointer base address is valid at dereference";
	public enum POINTER_BASE_VALIDITY { IGNORE, ASSUME, ASSERTandASSUME }
	public static final String LABEL_CHECK_POINTER_ALLOC = "Pointer to allocated memory at dereference";
	public enum POINTER_ALLOCATED { IGNORE, ASSUME, ASSERTandASSUME }
	public static final String LABEL_CHECK_FREE_VALID = "Check if freed pointer was valid";
	public static final String LABEL_CHECK_MemoryLeakInMain = "Check for the main procedure if all allocated memory was freed";
	public static final String LABEL_CHECK_MallocNonNegative = "Check if the input of malloc is non-negative";
	public static final String LABEL_REPORT_UNSOUNDNESS_WARNING = "Report unsoundness warnings";

	
	

}
