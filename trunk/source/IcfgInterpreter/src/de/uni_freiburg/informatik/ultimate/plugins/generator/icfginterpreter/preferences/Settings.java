package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.lang.reflect.InvocationTargetException;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader.LoadedClass;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.RNGChoice;

public class Settings {
	private final static Settings settings = new Settings();

	public static Settings getSettings() {
		return settings;
	}

	private final NonDeterministicChoice[] interfaceSet;

	public NonDeterministicChoice[] getInterfaces() {
		return interfaceSet.clone();
	}

	private Settings() {
		// TODO load stored implementations
		final String[] datas = {};
		interfaceSet = new NonDeterministicChoice[datas.length + 1];
		interfaceSet[0] = new RNGChoice(0);

		for (int i = 0; i < datas.length; i++) {
			final String data = datas[i];
			final LoadedClass implementation = LoadedClass.restoreClassData(data);
			try {
				interfaceSet[i + 1] = implementation.createInstance(NonDeterministicChoice.class, new Class<?>[0],
						new Object[0]);
			} catch (InstantiationException | IllegalAccessException | IllegalArgumentException
					| InvocationTargetException | NoSuchMethodException | SecurityException | ClassCastException e) {
				e.printStackTrace();
			}
		}
		// TODO query settings for selected interface
		ndc = interfaceSet[0];
	}

	public void storeNDCInterface(final LoadedClass implementation) {
		// TODO store implementation
	}

	private final NonDeterministicChoice ndc;

	public NonDeterministicChoice getNDC() {
		// final IPreferenceProvider preferences =
		// ICFGExecuterPreferences.getPreferences(IcfgInterpreter.getServices());

		return ndc;
	}
}