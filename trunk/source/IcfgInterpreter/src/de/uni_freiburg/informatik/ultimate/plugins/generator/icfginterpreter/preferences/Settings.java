package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.RNGChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences.SettingLabel;

public class Settings {
	private final static Settings settings = new Settings();

	public static Settings getSettings() {
		return settings;
	}

	private final Map<String, NonDeterministicChoice> interfaces;

	public List<NonDeterministicChoice> getInterfaces() {
		return new ArrayList<>(interfaces.values());
	}

	private Settings() {
		interfaces = Map.of(RNGChoice.class.getSimpleName(), new RNGChoice());
	}

	public NonDeterministicChoice getNDC() {
		final String chosenNDC = IcfgInterpreterPreferences.getPreferences()
				.getString(SettingLabel.NDC_IMLPEMENTATIONS.toString());

		return interfaces.get(chosenNDC);
	}
}