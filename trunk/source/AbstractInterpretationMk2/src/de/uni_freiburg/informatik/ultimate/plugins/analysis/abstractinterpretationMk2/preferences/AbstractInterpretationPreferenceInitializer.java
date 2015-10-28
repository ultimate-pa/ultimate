package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.preferences;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AIActivator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.AbstractDomainRegistry;

public class AbstractInterpretationPreferenceInitializer extends
		UltimatePreferenceInitializer {

	/*
	 * labels for the different preferences
	 */

	public static final String LABEL_MAIN_METHOD_NAMES = "Names of the program's main method (cs)";
	public static final String LABEL_ITERATIONS_UNTIL_WIDENING = "Minimum iterations before widening";
	public static final String LABEL_ITERATIONS_UNTIL_REC_WIDENING = "Minimum iterations before recursive widening";

	public static final String LABEL_STATES_UNTIL_MERGE = "Parallel states before merging";
	public static final String LABEL_POSTPONE_WIDENING = "Postpone execution of widened states";
	public static final String LABEL_WIDENING_FIXEDNUMBERS = "Set of numbers for widening (comma-separated list)";

	public static final String LABEL_WIDENING_AUTONUMBERS = "Collect literals from the RCFG's expressions";
	public static final String LABEL_STATE_ANNOTATIONS = "Save abstract states as node annotations";
	public static final String LABEL_LOGSTATES_CONSOLE = "Log state changes to console";
	public static final String LABEL_LOGSTATES_FILE = "Log state changes to file";
	public static final String LABEL_LOGSTATES_USESOURCEPATH = "Use source directory for state change logs";
	public static final String LABEL_LOGSTATES_PATH = "Directory for state change logs";

	public static final String LABEL_STOPAFTER = "Stop abstract interpretation after...";
	public static final String OPTION_STOPAFTER_ANYERROR = "any error location is reached";
	public static final String OPTION_STOPAFTER_ALLERRORS = "all error locations are reached";
	public static final String OPTION_STOPAFTER_FULLSTATESPACE = "full abstract state space is explored";
	public static final String[] OPTIONS_STOPAFTER = {
			OPTION_STOPAFTER_ANYERROR, OPTION_STOPAFTER_ALLERRORS,
			OPTION_STOPAFTER_FULLSTATESPACE };

	public static final String LABEL_DOMAIN = "Domain";

	public static final String LABEL_DOMAIN_MERGE = "Merge Operator";
	public static final String LABEL_DOMAIN_WIDENING = "Widening Operator";

	public static final String LABEL_INTFACTORY = "Factory for int";
	public static final String LABEL_REALFACTORY = "Factory for real";
	public static final String LABEL_BOOLFACTORY = "Factory for bool";
	public static final String LABEL_BITVECTORFACTORY = "Factory for BitVector";
	public static final String LABEL_STRINGFACTORY = "Factory for String";

	// %s -> domain ID
	public static final String LABEL_WIDENINGOP = "%s - Widening operator";
	public static final String LABEL_MERGEOP = "%s - Merge operator";

	/* --- default values for the different preferences --- */

	public static final String DEF_MAIN_METHOD_NAME = "Main, main";
	public static final int DEF_ITERATIONS_UNTIL_WIDENING = 3;
	public static final boolean DEF_POSTPONE_WIDENING = true;
	public static final int DEF_STATES_UNTIL_MERGE = 5;
	public static final String DEF_WIDENING_FIXEDNUMBERS = "0, 1, 3.14, -128, 127";
	public static final boolean DEF_WIDENING_AUTONUMBERS = false;

	public static final boolean DEF_STATE_ANNOTATIONS = false;
	public static final boolean DEF_LOGSTATES_CONSOLE = false;
	public static final boolean DEF_LOGSTATES_FILE = false;
	public static final boolean DEF_LOGSTATES_USESOURCEPATH = true;
	public static final String DEF_LOGSTATES_PATH = "./";

	public static final String DEF_STOPAFTER = OPTION_STOPAFTER_FULLSTATESPACE;

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		AbstractDomainRegistry domainRegistry = new AbstractDomainRegistry(null);

		List<UltimatePreferenceItem<?>> preferenceItems = new LinkedList<UltimatePreferenceItem<?>>();

		preferenceItems.add(new UltimatePreferenceItem<String>(
				"--- General preferences ---", null, PreferenceType.Label));

		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_MAIN_METHOD_NAMES, DEF_MAIN_METHOD_NAME,
				PreferenceType.String));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_POSTPONE_WIDENING, DEF_POSTPONE_WIDENING,
				PreferenceType.Boolean));

		preferenceItems
				.add(new UltimatePreferenceItem<Integer>(
						LABEL_ITERATIONS_UNTIL_WIDENING,
						DEF_ITERATIONS_UNTIL_WIDENING, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								1, 10000)));

		preferenceItems
				.add(new UltimatePreferenceItem<Integer>(
						LABEL_ITERATIONS_UNTIL_REC_WIDENING,
						DEF_ITERATIONS_UNTIL_WIDENING, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								1, 10000)));

		preferenceItems
				.add(new UltimatePreferenceItem<Integer>(
						LABEL_STATES_UNTIL_MERGE, DEF_STATES_UNTIL_MERGE,
						PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								1, 10000)));

		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_WIDENING_FIXEDNUMBERS, DEF_WIDENING_FIXEDNUMBERS,
				PreferenceType.String));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_WIDENING_AUTONUMBERS, DEF_WIDENING_AUTONUMBERS,
				PreferenceType.Boolean));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_STATE_ANNOTATIONS, DEF_STATE_ANNOTATIONS,
				PreferenceType.Boolean));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_LOGSTATES_CONSOLE, DEF_LOGSTATES_CONSOLE,
				PreferenceType.Boolean));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_LOGSTATES_FILE, DEF_LOGSTATES_FILE,
				PreferenceType.Boolean));

		preferenceItems.add(new UltimatePreferenceItem<Boolean>(
				LABEL_LOGSTATES_USESOURCEPATH, DEF_LOGSTATES_USESOURCEPATH,
				PreferenceType.Boolean));

		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_LOGSTATES_PATH, DEF_LOGSTATES_PATH,
				PreferenceType.Directory));

		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_STOPAFTER,
				DEF_STOPAFTER, PreferenceType.Combo, OPTIONS_STOPAFTER));

		// ------- Display Domains -------
		preferenceItems.add(new UltimatePreferenceItem<Integer>(
				"--- Domain Preferences ---", null, PreferenceType.Label));

		// collect valid domain IDs
		String[] validDomainIDs = new String[domainRegistry.getNofDomains()];
		Set<String> domainIDs = domainRegistry.getDomainIDs();
		{
			int i = 0;
			for (String id : domainIDs) {
				validDomainIDs[i] = id;
				i++;
			}
		}
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_DOMAIN,
				domainRegistry.getDefaultDomainID(), PreferenceType.Combo,
				validDomainIDs));

		// ------- Domains Widening Operators ------- //

		for (String id : domainIDs) {
			// widening operators
			Set<String> wideningOps = domainRegistry.getWideningOperators(id);
			if (wideningOps.size() > 0) {
				String[] validWideningOps = new String[wideningOps.size()];
				int i = 0;
				for (String op : wideningOps) {
					validWideningOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String
						.format(LABEL_WIDENINGOP, id), validWideningOps[0],
						PreferenceType.Combo, validWideningOps));
			}

			// merge operators
			Set<String> mergeOps = domainRegistry.getMergeOperators(id);
			if (mergeOps.size() > 0) {
				String[] validMergeOps = new String[mergeOps.size()];
				int i = 0;
				for (String op : mergeOps) {
					validMergeOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String
						.format(LABEL_MERGEOP, id), validMergeOps[0],
						PreferenceType.Combo, validMergeOps));
			}
		}

		// ------- ------- Display Factories ------- ------- //

		preferenceItems.add(new UltimatePreferenceItem<Integer>(
				"--- Preferences for the value domain ---", null,
				PreferenceType.Label));

		// collect valid value factory IDs
		String[] validFactoryIDs = new String[domainRegistry.getNofFactories()];
		Set<String> factoryIDs = domainRegistry.getValueFactoriyIDs();
		{

			int i = 0;
			for (String id : factoryIDs) {
				validFactoryIDs[i] = id;
				i++;
			}
		}

		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_INTFACTORY, domainRegistry.getDefaultFactoryIDForInt(),
				PreferenceType.Combo, validFactoryIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_REALFACTORY, domainRegistry.getDefaultFactoryIDForReal(),
				PreferenceType.Combo, validFactoryIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_BOOLFACTORY, domainRegistry.getDefaultFactoryIDForBool(),
				PreferenceType.Combo, validFactoryIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_BITVECTORFACTORY, domainRegistry
						.getDefaultFactoryIDForBitVector(),
				PreferenceType.Combo, validFactoryIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(
				LABEL_STRINGFACTORY, domainRegistry
						.getDefaultFactoryIDForString(), PreferenceType.Combo,
				validFactoryIDs));

		// preferences per abstract value factory system
		for (String id : factoryIDs) {
			preferenceItems
					.add(new UltimatePreferenceItem<Integer>(
							String.format(
									"--- Preferences for the %s value factory ---",
									id), null, PreferenceType.Label));

			// widening operators
			Set<String> wideningOps = domainRegistry
					.getValueWideningOperators(id);
			if (wideningOps.size() > 0) {
				String[] validWideningOps = new String[wideningOps.size()];
				int i = 0;
				for (String op : wideningOps) {
					validWideningOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String
						.format(LABEL_WIDENINGOP, id), validWideningOps[0],
						PreferenceType.Combo, validWideningOps));
			}

			// merge operators
			Set<String> mergeOps = domainRegistry.getValueMergeOperators(id);
			if (mergeOps.size() > 0) {
				String[] validMergeOps = new String[mergeOps.size()];
				int i = 0;
				for (String op : mergeOps) {
					validMergeOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String
						.format(LABEL_MERGEOP, id), validMergeOps[0],
						PreferenceType.Combo, validMergeOps));
			}
		}

		return preferenceItems.toArray(new UltimatePreferenceItem<?>[0]);
	}

	@Override
	protected String getPlugID() {
		return AIActivator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Abstract InterpretationMk2";
	}
}
