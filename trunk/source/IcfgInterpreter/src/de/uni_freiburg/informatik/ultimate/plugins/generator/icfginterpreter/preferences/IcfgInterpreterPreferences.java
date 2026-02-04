package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator.IntegerValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;

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
				new UltimatePreferenceItem<>(SettingLabel.EXECUTION_SEED.text(), 301796050, PreferenceType.Integer),
				new UltimatePreferenceItem<>(SettingLabel.OUTPUT_METHOD.text(), OutputMethod.DONT_PRINT,
						PreferenceType.Radio, OutputMethod.values()),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_PER_ENTRYPOINT.text(), 5, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.VARIANTS_PER_HAVOC_EDGE.text(), 3, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTIONS_QUEUED.text(), 128, PreferenceType.Integer,
						validatePositive),
				new UltimatePreferenceItem<>(SettingLabel.EXECUTION_MAX_LENGTH.text(), 1024, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),

				new UltimatePreferenceItem<>(SettingLabel.PARTIAL_RESULTS_COUNT.text(), 50, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				new UltimatePreferenceItem<>(SettingLabel.PARTIAL_RESULTS_STORE.text(), true, PreferenceType.Boolean),

				new UltimatePreferenceItem<>(SettingLabel.AGGREGATE_RESULTS_TYPE.text(),
						ExecutionTermintionReason.REACHED_ERROR, PreferenceType.Radio,
						ExecutionTermintionReason.values()),
				new UltimatePreferenceItem<>(SettingLabel.AGGREGATE_RESULTS_NUMBER.text(), 50, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				new UltimatePreferenceItem<>(SettingLabel.STOP_AFTER_AGGREGARE_FULL.text(), true,
						PreferenceType.Boolean),

				new UltimatePreferenceItem<>(SettingLabel.MIN_BITS.text(), 64, PreferenceType.Integer,
						new IntegerValidator(4, 2048)),
				new UltimatePreferenceItem<>(SettingLabel.MAX_BITS.text(), 64, PreferenceType.Integer,
						new IntegerValidator(4, 2048)),
				// ADD NEW SETTINGS HERE
		};

		return mainPrefs;
	}

	public enum OutputMethod {
		PRINT_TO_TERMINAL, PRINT_TO_FILE, DONT_PRINT
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
		OUTPUT_METHOD("How to print the created executions."
				+ " The executions are always passed to the next plug-in regardless of choice."),
		PARTIAL_RESULTS_COUNT(
				"Number of finished executions per output batch." + " (0 to output all executions at the end)"),
		PARTIAL_RESULTS_STORE("If enabled, finished executions will be discarded after the batch is processed."
				+ " They will not be passed to the next plug-in."),
		AGGREGATE_RESULTS_TYPE("For batches that are discarded after printing,"
				+ " some executions of this type will instead be stored and passed to the next plug-in."),
		AGGREGATE_RESULTS_NUMBER("The maximum number of executions of the chosen type to pass to the next plug-in"
				+ " if batches are discared after printing."),
		STOP_AFTER_AGGREGARE_FULL("If enabled, "
				+ "the plug-in will terminate as soon as the specified number of target executions is generated."),
		MIN_BITS("Havoc numbers are between 0 and -2^x + 1. (Bounds of the ICFG take priority over this setting.)"),
		MAX_BITS("Havoc numbers are between 0 and 2^x - 1. (Bounds of the ICFG take priority over this setting.)");

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