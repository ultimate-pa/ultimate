package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;

/**
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpretationPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_ITERATIONS_UNTIL_WIDENING = "Minimum iterations before widening";
	public static final String LABEL_STATES_UNTIL_MERGE = "Parallel states before merging";

	public static final int DEF_ITERATIONS_UNTIL_WIDENING = 10;
	public static final int DEF_STATES_UNTIL_MERGE = 2;

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem[] {
				new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS_UNTIL_WIDENING, DEF_ITERATIONS_UNTIL_WIDENING,
						PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(1, 100000)),
				new UltimatePreferenceItem<Integer>(LABEL_STATES_UNTIL_MERGE, DEF_STATES_UNTIL_MERGE,
						PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(1, 100000)),
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
