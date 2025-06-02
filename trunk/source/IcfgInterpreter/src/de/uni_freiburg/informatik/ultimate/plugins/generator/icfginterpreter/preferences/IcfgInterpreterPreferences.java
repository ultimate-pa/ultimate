package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator.IntegerValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;

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
		final IntegerValidator validatePositive = IUltimatePreferenceItemValidator.ONLY_POSITIVE_NON_ZERO;

		final BaseUltimatePreferenceItem[] mainPrefs = {
				new UltimatePreferenceItem<>(SettingLabel.EXECUTION_SEED.text(), -301796050, PreferenceType.Integer),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_PER_ENTRYPOINT.text(), 5, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.VARIANTS_PER_HAVOC_EDGE.text(), 3, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_QUEUED.text(), 1024, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTION_MAX_LENGTH.text(), 1024, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				new UltimatePreferenceItem<>(SettingLabel.BITS_HAVOCED.text(), 128, PreferenceType.Integer,
						new IntegerValidator(4, 2048)),
				// ADD NEW SETTINGS HERE
		};

		return mainPrefs;
	}

	/**
	 * The labels used for each settings, to enable easy value retrieval.
	 */
	public enum SettingLabel {
		EXECUTION_SEED("Seed to base non-determinsim on"),
		EXECUTIONS_PER_ENTRYPOINT("Number of differing executions to generate per program entry point"),
		VARIANTS_PER_HAVOC_EDGE("Number of differing executions to create when taking an edge with havoc"),
		EXECUTION_MAX_LENGTH("How many edges should be taken before the execution is terminated early? (0 for never)"),
		EXECUTIONS_QUEUED("Number of unfinished executions to store before disregarding new ones"),
		BITS_HAVOCED("Number of bits to havoc for integers. (Bounds of the ICFG take priority over this setting.)");

		private final String mText;

		SettingLabel(final String text) {
			mText = text;
		}

		public String text() {
			return mText;
		}

		@Override
		public String toString() {
			return mText;
		}
	}
}