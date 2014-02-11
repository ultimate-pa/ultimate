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

}
