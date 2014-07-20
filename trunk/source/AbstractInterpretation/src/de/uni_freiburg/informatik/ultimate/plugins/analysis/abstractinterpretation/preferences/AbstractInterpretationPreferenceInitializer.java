package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.preferences;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractDomainRegistry;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class AbstractInterpretationPreferenceInitializer extends
		UltimatePreferenceInitializer {

	/*
	 * labels for the different preferencess
	 */
	
	public static final String LABEL_ITERATIONS_UNTIL_WIDENING = "Minimum iterations before widening";
	public static final String LABEL_STATES_UNTIL_MERGE = "Parallel states before merging";
	public static final String LABEL_STATE_ANNOTATIONS = "Save abstract states as node annotations";
	
	public static final String LABEL_ABSTRACTDOMAIN = "Abstract domain for numbers";

	// %s -> domain ID
	public static final String LABEL_WIDENINGOP = "%s - Widening operator";
	public static final String LABEL_MERGEOP = "%s - Merge operator";

	/*
	 * default values for the different preferences
	 */

	public static final int DEF_ITERATIONS_UNTIL_WIDENING = 1;
	public static final int DEF_STATES_UNTIL_MERGE = 1;
	public static final boolean DEF_STATE_ANNOTATIONS = false;

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		
		List<UltimatePreferenceItem<?>> preferenceItems = new LinkedList<UltimatePreferenceItem<?>>();

		preferenceItems.add(new UltimatePreferenceItem<Integer>("--- General preferences ---",
				null, PreferenceType.Label));
		
		preferenceItems.add(new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS_UNTIL_WIDENING,
				DEF_ITERATIONS_UNTIL_WIDENING, PreferenceType.Integer,
				new IUltimatePreferenceItemValidator.IntegerValidator(1, 10000)));
		preferenceItems.add(new UltimatePreferenceItem<Integer>(LABEL_STATES_UNTIL_MERGE,
				DEF_STATES_UNTIL_MERGE, PreferenceType.Integer,
				new IUltimatePreferenceItemValidator.IntegerValidator(1, 10000)));
		preferenceItems.add(new UltimatePreferenceItem<Boolean>(LABEL_STATE_ANNOTATIONS,
								DEF_STATE_ANNOTATIONS, PreferenceType.Boolean));
		
		// collect valid domain IDs
		Collection<String> domainIDs = AbstractDomainRegistry.getDomainFactories().keySet();
		String[] validDomainIDs = new String[domainIDs.size()];
		int i = 0;
		for (String id : domainIDs) {
			validDomainIDs[i] = id;
			i++;
		}
		preferenceItems.add(new UltimatePreferenceItem<String>(LABEL_ABSTRACTDOMAIN, validDomainIDs[0],
						PreferenceType.Combo, validDomainIDs));

		// preferences per abstract domain system
		for (String id : domainIDs) {
			preferenceItems.add(new UltimatePreferenceItem<Integer>(
					String.format("--- Preferences for the %s domain ---", id),
					null, PreferenceType.Label));
			
			// widening operators
			Collection<String> wideningOps = AbstractDomainRegistry.getWideningOperators(id).keySet();
			String[] validWideningOps = new String[wideningOps.size()];
			i = 0;
			for (String op : wideningOps) {
				validWideningOps[i] = op;
				i++;
			}
			preferenceItems.add(new UltimatePreferenceItem<String>(String.format(LABEL_WIDENINGOP, id),
					validWideningOps[0], PreferenceType.Combo, validWideningOps));
			
			// merge operators
			Collection<String> mergeOps = AbstractDomainRegistry.getMergeOperators(id).keySet();
			String[] validMergeOps = new String[mergeOps.size()];
			i = 0;
			for (String op : mergeOps) {
				validMergeOps[i] = op;
				i++;
			}
			preferenceItems.add(new UltimatePreferenceItem<String>(String.format(LABEL_MERGEOP, id),
					validMergeOps[0], PreferenceType.Combo, validMergeOps));
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
