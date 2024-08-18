package de.uni_freiburg.informatik.ultimate.witnessparser.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.Activator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessParserPreferences extends UltimatePreferenceInitializer {

	public static final String LABEL_CW_USE_ONLY_LOOPINVARIANTS = "Only consider loop invariants";
	private static final boolean DEF_CW_USE_ONLY_LOOPINVARIANTS = true;
	private static final String DESC_CW_USE_ONLY_LOOPINVARIANTS =
			"When reading correctness witnesses in GraphML, only consider invariants at nodes that can be entered with a transition that is labeled with enterLoopHead=true";

	public static final String LABEL_IGNORE_UNMATCHED_WITNESS_ENTRIES =
			"Ignore witness entries that could not be matched";
	private static final boolean DEF_IGNORE_UNMATCHED_WITNESS_ENTRIES = false;
	private static final String DESC_IGNORE_UNMATCHED_WITNESS_ENTRIES =
			"If set to true we ignore witness entries that could not be matched silently. Otherwise we throw an exception.";

	public WitnessParserPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	public static IPreferenceProvider getPrefs(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {

				new UltimatePreferenceItem<>(LABEL_CW_USE_ONLY_LOOPINVARIANTS, DEF_CW_USE_ONLY_LOOPINVARIANTS,
						DESC_CW_USE_ONLY_LOOPINVARIANTS, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_IGNORE_UNMATCHED_WITNESS_ENTRIES,
						DEF_IGNORE_UNMATCHED_WITNESS_ENTRIES, DESC_IGNORE_UNMATCHED_WITNESS_ENTRIES,
						PreferenceType.Boolean) };
	}

}
