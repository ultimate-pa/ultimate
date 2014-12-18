package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.preferences;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;

public class AbstractInterpretationPreferenceInitializer extends
		UltimatePreferenceInitializer {

	/*
	 * labels for the different preferences
	 */

	public static final String LABEL_MAIN_METHOD_NAME = "Name of the program's main method";
	public static final String LABEL_ITERATIONS_UNTIL_WIDENING = "Minimum iterations before widening";
	public static final String LABEL_STATES_UNTIL_MERGE = "Parallel states before merging";
	public static final String LABEL_WIDENING_FIXEDNUMBERS = "Set of numbers for widening (comma-separated list)";
	public static final String LABEL_WIDENING_AUTONUMBERS = "Collect literals from the RCFG's expressions";

	public static final String LABEL_STATE_ANNOTATIONS = "Save abstract states as node annotations";
	public static final String LABEL_LOGSTATES_CONSOLE = "Log state changes to console";
	public static final String LABEL_LOGSTATES_FILE = "Log state changes to file";
	public static final String LABEL_LOGSTATES_USESOURCEPATH = "Use source directory for state change logs";
	public static final String LABEL_LOGSTATES_PATH = "Directory for state change logs";

	public static final String LABEL_STOPAFTER = "Stop abstract interpretation after...";
	public static final String  OPTION_STOPAFTER_ANYERROR = "any error location is reached";
	public static final String  OPTION_STOPAFTER_ALLERRORS = "all error locations are reached";
	public static final String  OPTION_STOPAFTER_FULLSTATESPACE = "full abstract state space is explored";
	public static final String[] OPTIONS_STOPAFTER = {OPTION_STOPAFTER_ANYERROR,
		OPTION_STOPAFTER_ALLERRORS, OPTION_STOPAFTER_FULLSTATESPACE};

	public static final String LABEL_INTDOMAIN = "Domain for int";
	public static final String LABEL_REALDOMAIN = "Domain for real";
	public static final String LABEL_BOOLDOMAIN = "Domain for bool";
	public static final String LABEL_BITVECTORDOMAIN = "Domain for BitVector";
	public static final String LABEL_STRINGDOMAIN = "Domain for String";

	// %s -> domain ID
	public static final String LABEL_WIDENINGOP = "%s - Widening operator";
	public static final String LABEL_MERGEOP = "%s - Merge operator";

	/*
	 * default values for the different preferences
	 */

	public static final String DEF_MAIN_METHOD_NAME = "Main";
	public static final int DEF_ITERATIONS_UNTIL_WIDENING = 2;
	public static final int DEF_STATES_UNTIL_MERGE = 1;
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
		AbstractDomainRegistry domainRegistry = new AbstractDomainRegistry();
		
		List<UltimatePreferenceItem<?>> preferenceItems = new LinkedList<UltimatePreferenceItem<?>>();

		preferenceItems.add(new UltimatePreferenceItem<Integer>("--- General preferences ---",
				null, PreferenceType.Label));

		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_MAIN_METHOD_NAME,
				DEF_MAIN_METHOD_NAME, PreferenceType.String));
		preferenceItems.add(new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS_UNTIL_WIDENING,
				DEF_ITERATIONS_UNTIL_WIDENING, PreferenceType.Integer,
				new IUltimatePreferenceItemValidator.IntegerValidator(1, 10000)));
		preferenceItems.add(new UltimatePreferenceItem<Integer>(LABEL_STATES_UNTIL_MERGE,
				DEF_STATES_UNTIL_MERGE, PreferenceType.Integer,
				new IUltimatePreferenceItemValidator.IntegerValidator(1, 10000)));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_WIDENING_FIXEDNUMBERS,
				DEF_WIDENING_FIXEDNUMBERS, PreferenceType.String));
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_WIDENING_AUTONUMBERS,
				DEF_WIDENING_AUTONUMBERS, PreferenceType.Boolean));
		
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_STATE_ANNOTATIONS,
								DEF_STATE_ANNOTATIONS, PreferenceType.Boolean));
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_LOGSTATES_CONSOLE,
				DEF_LOGSTATES_CONSOLE, PreferenceType.Boolean));
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_LOGSTATES_FILE,
				DEF_LOGSTATES_FILE, PreferenceType.Boolean));
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_LOGSTATES_USESOURCEPATH,
				DEF_LOGSTATES_USESOURCEPATH, PreferenceType.Boolean));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_LOGSTATES_PATH,
				DEF_LOGSTATES_PATH, PreferenceType.Directory));
		
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_STOPAFTER, DEF_STOPAFTER,
				PreferenceType.Combo, OPTIONS_STOPAFTER));
		
		// collect valid domain IDs
		Set<String> domainIDs = domainRegistry.getDomainIDs();
		String[] validDomainIDs = new String[domainIDs.size()];
		int i = 0;
		for (String id : domainIDs) {
			validDomainIDs[i] = id;
			i++;
		}
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_INTDOMAIN, domainRegistry.getDefaultDomainIDForInt(),
						PreferenceType.Combo, validDomainIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_REALDOMAIN, domainRegistry.getDefaultDomainIDForReal(),
				PreferenceType.Combo, validDomainIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_BOOLDOMAIN, domainRegistry.getDefaultDomainIDForBool(),
				PreferenceType.Combo, validDomainIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_BITVECTORDOMAIN, domainRegistry.getDefaultDomainIDForBitVector(),
				PreferenceType.Combo, validDomainIDs));
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_STRINGDOMAIN, domainRegistry.getDefaultDomainIDForString(),
				PreferenceType.Combo, validDomainIDs));

		// preferences per abstract domain system
		for (String id : domainIDs) {
			preferenceItems.add(new UltimatePreferenceItem<Integer>(
					String.format("--- Preferences for the %s domain ---", id),
					null, PreferenceType.Label));
			
			// widening operators
			Set<String> wideningOps = domainRegistry.getWideningOperators(id);
			if (wideningOps.size() > 0) {
				String[] validWideningOps = new String[wideningOps.size()];
				i = 0;
				for (String op : wideningOps) {
					validWideningOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String.format(LABEL_WIDENINGOP, id),
						validWideningOps[0], PreferenceType.Combo, validWideningOps));
			}
			
			// merge operators
			Set<String> mergeOps = domainRegistry.getMergeOperators(id);
			if (mergeOps.size() > 0) {
				String[] validMergeOps = new String[mergeOps.size()];
				i = 0;
				for (String op : mergeOps) {
					validMergeOps[i] = op;
					i++;
				}
				preferenceItems.add(new UltimatePreferenceItem<String>(String.format(LABEL_MERGEOP, id),
						validMergeOps[0], PreferenceType.Combo, validMergeOps));
			}
		}
		
		return preferenceItems.toArray(new UltimatePreferenceItem<?>[0]);
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Abstract Interpretation";
	}
}
