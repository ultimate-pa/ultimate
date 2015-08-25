package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval.IntervalSimpleWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomain;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpretationPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String[] VALUES_ABSTRACT_DOMAIN = new String[] { EmptyDomain.class.getSimpleName(),
	        SignDomain.class.getSimpleName(), IntervalDomain.class.getSimpleName() };

	public static final String[] VALUES_WIDENING_OPERATOR = new String[] { IntervalSimpleWideningOperator.class
	        .getSimpleName() };

	public static final String LABEL_ITERATIONS_UNTIL_WIDENING = "Minimum iterations before widening";
	public static final String LABEL_STATES_UNTIL_MERGE = "Parallel states before merging";
	public static final String LABEL_ABSTRACT_DOMAIN = "Abstract domain";
	public static final String LABEL_INTERVAL_WIDENING_OPERATOR = "Widening operator";
	public static final String LABEL_INTERVAL_DOMAIN_SEPARATOR = "   ---   Interval Domain   ---   ";

	public static final int DEF_ITERATIONS_UNTIL_WIDENING = 10;
	public static final int DEF_STATES_UNTIL_MERGE = 2;
	public static final String DEF_ABSTRACT_DOMAIN = VALUES_ABSTRACT_DOMAIN[0];
	public static final String DEF_WIDENING_OPERATOR = VALUES_WIDENING_OPERATOR[0];

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		ArrayList<UltimatePreferenceItem<?>> rtr = new ArrayList<UltimatePreferenceItem<?>>();
		rtr.add(new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS_UNTIL_WIDENING, DEF_ITERATIONS_UNTIL_WIDENING,
		        PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(1, 100000)));
		rtr.add(new UltimatePreferenceItem<Integer>(LABEL_STATES_UNTIL_MERGE, DEF_STATES_UNTIL_MERGE,
		        PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(1, 100000)));
		rtr.add(new UltimatePreferenceItem<String>(LABEL_ABSTRACT_DOMAIN, DEF_ABSTRACT_DOMAIN, PreferenceType.Combo,
		        VALUES_ABSTRACT_DOMAIN));

		rtr.add(new UltimatePreferenceItem<String>(LABEL_INTERVAL_DOMAIN_SEPARATOR, null, PreferenceType.Label));

		rtr.add(new UltimatePreferenceItem<String>(LABEL_INTERVAL_WIDENING_OPERATOR, DEF_WIDENING_OPERATOR,
		        PreferenceType.Combo, VALUES_WIDENING_OPERATOR));

		return rtr.toArray(new UltimatePreferenceItem<?>[rtr.size()]);
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}

}
