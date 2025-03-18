package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

public class ICFGExecuterPreferences extends UltimatePreferenceInitializer {
	public ICFGExecuterPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		final NonDeterministicChoice[] interfaces = Settings.getSettings().getInterfaces();
		final UltimatePreferenceItemGroup[] subPrefs = new UltimatePreferenceItemGroup[interfaces.length];
		final String[] names = new String[interfaces.length];

		for (int i = 0; i < interfaces.length; i++) {
			names[i] = interfaces[i].getClass().getSimpleName();
			subPrefs[i] = interfaces[i].getImplementationSettings();
		}

		final BaseUltimatePreferenceItem[] mainPrefs = {
				new UltimatePreferenceItem<>(PROJECT_DIRECTORY_LABEL, projectDirectory.getAbsolutePath(),
						PROJECT_DIRECTORY_HINT, PreferenceType.Directory),
				new UltimatePreferenceItem<>(NDC_IMLPEMENTATIONS_LABEL, interfaces[0], NDC_IMLPEMENTATIONS_HINT,
						PreferenceType.Radio, names),
				// ADD NEW SETTINGS HERE
				new UltimatePreferenceItem<>("Non-Deterministic Interface specific settings:", null,
						PreferenceType.Label) };

		final BaseUltimatePreferenceItem[] allPrefs = new BaseUltimatePreferenceItem[mainPrefs.length
				+ subPrefs.length];

		for (int i = 0; i < mainPrefs.length; i++) {
			allPrefs[i] = mainPrefs[i];
		}

		for (int i = 0; i < subPrefs.length; i++) {
			allPrefs[i + mainPrefs.length] = subPrefs[i];
		}

		return allPrefs;
	}

	public static IPreferenceProvider getPreferences(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	private final static File projectDirectory = new File(
			DynamicLoader.class.getProtectionDomain().getCodeSource().getLocation().getPath());

	/**
	 * @return The file pointing to the base directory of this plug-in: <br>
	 *         Like .../ultimate/trunk/source/IcfgInterpreter/
	 */
	public static File getProjectSourceDirectory() {
		return projectDirectory;
	}

	public static String PROJECT_DIRECTORY_LABEL = "Ultimate directory";
	public static String PROJECT_DIRECTORY_HINT = "Path of directory which contains the /ultimate/ directory";

	public static String NDC_IMLPEMENTATIONS_LABEL = "Non-Deterministic Interface implementations:";
	public static String NDC_IMLPEMENTATIONS_HINT = "Class to use for methods like havoc.";
}