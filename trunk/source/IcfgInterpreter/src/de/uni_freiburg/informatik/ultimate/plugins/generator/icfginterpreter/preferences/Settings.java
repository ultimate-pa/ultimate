package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader.LoadedClass;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.RNGChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences.SettingLabel;

public class Settings {
	private final static Settings settings = new Settings();

	public static Settings getSettings() {
		return settings;
	}

	private final HashMap<String, NonDeterministicChoice> interfaces;

	public ArrayList<NonDeterministicChoice> getInterfaces() {
		return new ArrayList<>(interfaces.values());
	}

	private Settings() {
		// TODO load stored implementations
		final String[] datas = {};
		interfaces = new HashMap<>();
		interfaces.put(RNGChoice.class.getSimpleName(), new RNGChoice());

		for (final String data : datas) {
			final LoadedClass implementation = LoadedClass.restoreClassData(data);
			try {
				final NonDeterministicChoice next = implementation.createInstance(NonDeterministicChoice.class,
						new Class<?>[0], new Object[0]);
				interfaces.put(next.getClass().getSimpleName(), next);

			} catch (InstantiationException | IllegalAccessException | IllegalArgumentException
					| InvocationTargetException | NoSuchMethodException | SecurityException | ClassCastException e) {
				e.printStackTrace();
			}
		}
	}

	public void storeNDCInterface(final LoadedClass implementation) {
		// TODO store implementation
	}

	public NonDeterministicChoice getNDC() {
		// final IPreferenceProvider preferences =
		// ICFGExecuterPreferences.getPreferences(IcfgInterpreter.getServices());
		final String chosenNDC = IcfgInterpreterPreferences.getPreferences()
				.getString(SettingLabel.NDC_IMLPEMENTATIONS.toString());

		return interfaces.get(chosenNDC);
	}
}