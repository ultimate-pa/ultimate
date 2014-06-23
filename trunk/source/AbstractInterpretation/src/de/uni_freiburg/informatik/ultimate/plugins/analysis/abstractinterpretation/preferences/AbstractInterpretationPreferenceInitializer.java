package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.preferences;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class AbstractInterpretationPreferenceInitializer extends
		UltimatePreferenceInitializer {

	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_BOOLEAN = "BOOLEAN";
	public static final String LABEL_INTEGER = "INTEGER";
	public static final String LABEL_PATHSTRING = "PATH STRING";
	public static final String LABEL_STRINGLIST = "STRING LIST";

	/*
	 * default values for the different preferences
	 */
	public static final boolean DEF_BOOLEAN = true;
	public static final int DEF_INTEGER = 1000;
	public static final String DEF_PATHSTRING = ".";
	public static final String DEF_STRINGLIST = "a";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_BOOLEAN,
						DEF_BOOLEAN, PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(LABEL_INTEGER,
						DEF_INTEGER, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 10000)),
				new UltimatePreferenceItem<String>(LABEL_PATHSTRING,
						DEF_PATHSTRING, PreferenceType.Directory),
				new UltimatePreferenceItem<String>(LABEL_STRINGLIST, DEF_STRINGLIST,
						PreferenceType.Combo, new String[] {"a", "b", "c"})
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Abstract Interpretation";
	}
}
