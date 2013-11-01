package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.Activator;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Integer>(Name_Timeout,
						Default_Timeout, PreferenceType.Integer,
						new TimeoutValidator()),
				new UltimatePreferenceItem<Boolean>(Name_WriteToFile,
						Default_WriteToFile, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(Name_Path, Default_Path,
						PreferenceType.Directory)
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Automata Script Interpreter";
	}

	public static final String Name_WriteToFile = "Write results of print operation to file";
	public static final boolean Default_WriteToFile = false;

	public static final String Name_Path = "Directory";
	public static final String Default_Path = ".";

	public static final String Name_Timeout = "Timeout";
	public static final int Default_Timeout = 60;

	private class TimeoutValidator implements
			IUltimatePreferenceItemValidator<Integer> {

		@Override
		public boolean isValid(Integer value) {
			return 0 <= value && value <= 10000000;
		}

		@Override
		public String getInvalidValueErrorMessage(Integer value) {
			return "Valid range is 0 <= value <= 10000000";
		}

	}

}
