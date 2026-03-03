package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator.IntegerValidator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;

public class IcfgInterpreterPreferences extends UltimatePreferenceInitializer {
	public static final String EXECUTION_SEED = "Seed to base non-determinsim on";
	public static final String EXECUTIONS_PER_ENTRYPOINT =
			"Number of differing executions to generate per program entry point";
	public static final String VARIANTS_PER_HAVOC_EDGE =
			"Number of differing executions to create when taking an edge with havoc";
	public static final String EXECUTION_MAX_LENGTH =
			"How many edges should be taken before the execution is terminated early? (0 for never)";
	public static final String EXECUTIONS_QUEUED =
			"Number of unfinished executions to store before disregarding new ones";
	public static final String OUTPUT_METHOD =
			"How to print the created executions. The executions are always passed to the next plug-in regardless of "
					+ "choice.";
	public static final String PARTIAL_RESULTS_COUNT =
			"Number of finished executions per output batch." + " (0 to output all executions at the end)";
	public static final String PARTIAL_RESULTS_STORE =
			"If enabled, finished executions will be discarded after the batch is processed. They will not be passed "
					+ "to the next plug-in.";
	public static final String AGGREGATE_RESULTS_TYPE =
			"For batches that are discarded after printing, some executions of this type will instead be stored and "
					+ "passed to the next plug-in.";
	public static final String AGGREGATE_RESULTS_NUMBER =
			"The maximum number of executions of the chosen type to pass to the next plug-in if batches are discared "
					+ "after printing.";
	public static final String STOP_AFTER_AGGREGARE_FULL =
			"If enabled, the plug-in will terminate as soon as the specified number of target executions is generated.";
	public static final String MIN_BITS =
			"Havoc numbers are between 0 and -2^x + 1. (Bounds of the ICFG take priority over this setting.)";
	public static final String MAX_BITS =
			"Havoc numbers are between 0 and 2^x - 1. (Bounds of the ICFG take priority over this setting.)";

	public IcfgInterpreterPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		final IntegerValidator validatePositive = IUltimatePreferenceItemValidator.ONLY_POSITIVE_NON_ZERO;

		final BaseUltimatePreferenceItem[] mainPrefs = {
				new UltimatePreferenceItem<>(OUTPUT_METHOD, OutputMethod.DONT_PRINT, PreferenceType.Radio,
						OutputMethod.values()),
				new UltimatePreferenceItem<>(EXECUTIONS_PER_ENTRYPOINT, 5, PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(VARIANTS_PER_HAVOC_EDGE, 3, PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(EXECUTIONS_QUEUED, 128, PreferenceType.Integer, validatePositive),
				new UltimatePreferenceItem<>(EXECUTION_MAX_LENGTH, 1024, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),

				new UltimatePreferenceItem<>(PARTIAL_RESULTS_COUNT, 50, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				new UltimatePreferenceItem<>(PARTIAL_RESULTS_STORE, true, PreferenceType.Boolean),

				new UltimatePreferenceItem<>(AGGREGATE_RESULTS_TYPE, ExecutionTermintionReason.REACHED_ERROR,
						PreferenceType.Radio, ExecutionTermintionReason.values()),
				new UltimatePreferenceItem<>(AGGREGATE_RESULTS_NUMBER, 50, PreferenceType.Integer,
						IUltimatePreferenceItemValidator.ONLY_POSITIVE),
				new UltimatePreferenceItem<>(STOP_AFTER_AGGREGARE_FULL, true, PreferenceType.Boolean),

				new UltimatePreferenceItem<>(MIN_BITS, 64, PreferenceType.Integer, new IntegerValidator(4, 2048)),
				new UltimatePreferenceItem<>(MAX_BITS, 64, PreferenceType.Integer, new IntegerValidator(4, 2048)), };

		return mainPrefs;
	}

	public enum OutputMethod {
		PRINT_TO_TERMINAL, PRINT_TO_FILE, DONT_PRINT
	}
}