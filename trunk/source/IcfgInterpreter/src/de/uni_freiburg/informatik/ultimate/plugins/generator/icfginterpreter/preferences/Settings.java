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
		final String[] datas = {}; // TODO load stored implementations
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
	}

	public void storeNDCInterface(final LoadedClass implementation) {
		// interfaceSet.add(implementation.getClassObject());
		// String data = implementation.encodeClassData();
		// TODO store
		// add name to file that keeps track of all external implementations
		// add file with data needed to recreate the class later, by either re-compiling or using existing .class file
		// do not overwrite external file, instead:
		// 1. Make temp file to write to
		// 2. Copy contents to original File
		// 3. Delete temp
		// Should something go wrong, either the temp or original should be valid
	}

	private NonDeterministicChoice ndc;

	public NonDeterministicChoice getNDC() {
		// final IPreferenceProvider preferences =
		// ICFGExecuterPreferences.getPreferences(IcfgInterpreter.getServices());

		return ndc;
	}
}