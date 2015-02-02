package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String OPTIMIZE_SBE = "Use small block encoding for initial RCFG";
	public static final String OPTIMIZE_MAXIMIZE_FINAL_STATES = "Maximize final states of the product";
	public static final String OPTIMIZE_MINIMIZE_LINEAR_STATES = "Minimize linear states of the product";
	public static final String OPTIMIZE_REMOVE_INFEASIBLE_EDGES = "Remove infeasible edges from the product";
	public static final String OPTIMIZE_SIMPLIFY_ASSUMES = "Simplify assume statements";
	public static final String OPTIMIZE_UNTIL_FIXPOINT = "Apply product optimizations until nothing changes";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>("RCFG Optimizations", "", PreferenceType.Label),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_SBE, true, PreferenceType.Boolean),
				
				new UltimatePreferenceItem<String>("Product Optimizations", "", PreferenceType.Label),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_MAXIMIZE_FINAL_STATES, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_MINIMIZE_LINEAR_STATES, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_REMOVE_INFEASIBLE_EDGES, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_SIMPLIFY_ASSUMES, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(OPTIMIZE_UNTIL_FIXPOINT, true, PreferenceType.Boolean), 
				
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}
}