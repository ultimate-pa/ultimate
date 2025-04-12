package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IcfgInterpreterPreferences extends UltimatePreferenceInitializer {
	private static RcpPreferenceProvider mSettings = null;

	public IcfgInterpreterPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	/**
	 * Replace the preference provider returned by {@link #getPreferences()} with a new instance to reflect any changes.
	 */
	public static void updatePreferences() {
		mSettings = new RcpPreferenceProvider(Activator.PLUGIN_ID);
	}

	public static RcpPreferenceProvider getPreferences() {
		return mSettings;
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		final ArrayList<NonDeterministicChoice> interfaces = Settings.getSettings().getInterfaces();
		final ArrayList<UltimatePreferenceItemGroup> subPrefs = new ArrayList<>();
		final String[] names = new String[interfaces.size()];

		for (int i = 0; i < interfaces.size(); i++) {
			names[i] = interfaces.get(i).getClass().getSimpleName();
			final UltimatePreferenceItemGroup settings = interfaces.get(i).getImplementationSettings();
			if (settings == null) {
				continue;
			}
			subPrefs.add(settings);
		}

		final BaseUltimatePreferenceItem[] mainPrefs = {
				new UltimatePreferenceItem<>(SettingLabel.PROJECT_DIRECTORY.toString(),
						DynamicLoader.getProjectSourceDirectory().getAbsolutePath(), PROJECT_DIRECTORY_HINT,
						PreferenceType.Directory),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_PER_ENTRYPOINT.toString(), 5, EXECUTIONS_PE_HINT,
						PreferenceType.Integer),
				// ADD NEW SETTINGS HERE
				new UltimatePreferenceItem<>(SettingLabel.NDC_IMLPEMENTATIONS.toString(), names[0],
						NDC_IMLPEMENTATIONS_HINT, PreferenceType.Radio, names) };

		final BaseUltimatePreferenceItem[] allPrefs = new BaseUltimatePreferenceItem[mainPrefs.length + 1];

		for (int i = 0; i < mainPrefs.length; i++) {
			allPrefs[i] = mainPrefs[i];
		}

		allPrefs[mainPrefs.length] = new UltimatePreferenceItemContainer(
				"Non-Deterministic Interface specific settings",
				Util.fillArray(subPrefs, new UltimatePreferenceItemGroup[subPrefs.size()]));
		return allPrefs;
	}

	/**
	 * The labels used for each settings, to enable easy value retrieval.
	 */
	public enum SettingLabel {
		PROJECT_DIRECTORY("Ultimate directory"),
		NDC_IMLPEMENTATIONS(
				"Non-Deterministic Interface (" + NonDeterministicChoice.class.getSimpleName() + ") implementations:"),
		EXECUTIONS_PER_ENTRYPOINT("Number of executions to generate per program entry point");

		private final String mText;

		SettingLabel(final String text) {
			mText = text;
		}

		@Override
		public String toString() {
			return mText;
		}
	}

	public static String PROJECT_DIRECTORY_HINT = "Path of directory which contains the /ultimate/ directory";
	public static String NDC_IMLPEMENTATIONS_HINT = "Class to use for methods like havoc.";
	public static String EXECUTIONS_PE_HINT = "Should be at least 1";
}