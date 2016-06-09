package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

public class PreferenceInitializer extends UltimatePreferenceInitializer {
	
	
	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_ID);
	}

	public static enum PatternTransformerTypes { 
		None, ClosedWorld, SimplePositiveTest, 
		};
	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_TRANSFORMER = "Transformer";

	/*
	 * default values for the different preferences
	 */

	public static final PatternTransformerTypes DEF_TRANSFORMER = PatternTransformerTypes.None;

	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new BaseUltimatePreferenceItem[] {
				new UltimatePreferenceItem<PatternTransformerTypes>(LABEL_TRANSFORMER, DEF_TRANSFORMER, PreferenceType.Combo
						,PatternTransformerTypes.values()),
				};
	}

}














