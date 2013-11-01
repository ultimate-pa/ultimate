package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {
				new UltimatePreferenceItem<Boolean>(LABEL_CALLMINIMIZE, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_EXECUTETESTS, false,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<RatingStrategy>(LABEL_STRATEGY,
						RatingStrategy.DEFAULT, PreferenceType.Combo,
						RatingStrategy.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_USESTATHEURISTIC,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_USEDYNAMICHEURISTIC,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_RATINGBOUND, "",
						PreferenceType.String),

		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Block Encoding";
	}

	public static final String LABEL_CALLMINIMIZE = "Minimize Call and Return Edges";

	public static final String LABEL_EXECUTETESTS = "Execute Unit-Tests, with special Observer";

	public static final String LABEL_STRATEGY = "Choose the strategy for the edge rating:";

	public static final String LABEL_RATINGBOUND = "Enter Rating-Boundary (empty for LBE):";

	public static final String LABEL_USESTATHEURISTIC = "Enable Statistic-Based Heuristic: ";

	public static final String LABEL_USEDYNAMICHEURISTIC = "Enable Dynamic-Based Heuristic: ";

}
