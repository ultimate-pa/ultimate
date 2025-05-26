package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator.IntegerValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;

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
		final List<NonDeterministicChoice> interfaces = Settings.getSettings().getInterfaces();
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

		final IntegerValidator validatePositive = IUltimatePreferenceItemValidator.ONLY_POSITIVE_NON_ZERO;

		final BaseUltimatePreferenceItem[] mainPrefs = {
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_PER_ENTRYPOINT.text(), 5,
						SettingLabel.EXECUTIONS_PER_ENTRYPOINT.hint(), PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.VARIANTS_PER_HAVOC_EDGE.text(), 3,
						SettingLabel.VARIANTS_PER_HAVOC_EDGE.hint(), PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_QUEUED.text(), 1024,
						SettingLabel.EXECUTIONS_QUEUED.hint(), PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTION_MAX_LENGTH.text(), 1024,
						SettingLabel.EXECUTION_MAX_LENGTH.hint(), PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				// ADD NEW SETTINGS HERE
				new UltimatePreferenceItem<>(SettingLabel.NDC_IMLPEMENTATIONS.text(), names[0],
						SettingLabel.NDC_IMLPEMENTATIONS.hint(), PreferenceType.Radio, names), };

		final BaseUltimatePreferenceItem[] allPrefs = new BaseUltimatePreferenceItem[mainPrefs.length + 1];

		for (int i = 0; i < mainPrefs.length; i++) {
			allPrefs[i] = mainPrefs[i];
		}

		allPrefs[mainPrefs.length] = new UltimatePreferenceItemContainer(
				"Non-Deterministic Interface specific settings",
				subPrefs.toArray(new UltimatePreferenceItemGroup[subPrefs.size()]));
		return allPrefs;
	}

	/**
	 * The labels used for each settings, to enable easy value retrieval.
	 */
	public enum SettingLabel {
		NDC_IMLPEMENTATIONS(
				"Non-Deterministic Interface (" + NonDeterministicChoice.class.getSimpleName() + ") implementations:",
				"Class to use for methods like havoc."),
		EXECUTIONS_PER_ENTRYPOINT("Number of differing executions to generate per program entry point",
				"Should be at least 1"),
		VARIANTS_PER_HAVOC_EDGE("Number of differing executions to create when taking an edge with havoc.",
				"Should be at least 1"),
		EXECUTION_MAX_LENGTH("How many edges shouldbe taken before the execution is terminated early? (0 for never)",
				"Should be at least 0"),
		EXECUTIONS_QUEUED("Number of unfinished executions to store before disregarding new ones",
				"Should be at least 1");

		private final String mText;
		private final String mHint;

		SettingLabel(final String text, final String hint) {
			mText = text;
			mHint = hint;
		}

		public String text() {
			return mText;
		}

		public String hint() {
			return mHint;
		}

		@Override
		public String toString() {
			return mText;
		}
	}
}