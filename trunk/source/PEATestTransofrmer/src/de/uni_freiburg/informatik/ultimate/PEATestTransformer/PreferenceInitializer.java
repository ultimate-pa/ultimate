package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType; 


public class PreferenceInitializer extends UltimatePreferenceInitializer {
	
	
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

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<PatternTransformerTypes>(LABEL_TRANSFORMER, DEF_TRANSFORMER, PreferenceType.Combo
						,PatternTransformerTypes.values()),
				};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_ID;
	}

}
