package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class OctPreferences {
	
	public static enum WideningOperator {
		SIMPLE, EXPONENTIAL, LITERAL;
	}

	public static final String WIDENING_OPERATOR = "Octagon widening operator";
	public static final WideningOperator WIDENING_OPERATOR_DEFAULT = WideningOperator.EXPONENTIAL;
	
	public static final String EXP_WIDENING_THRESHOLD = "Threshold for exponential widening";
	public static final String EXP_WIDENING_THRESHOLD_DEFAULT_VALUE = Integer.toString(Integer.MAX_VALUE);
	public static final String EXP_WIDENING_THRESHOLD_TOOLTIP
			= "Exponential widening will set values above this threshold to infinity";

	public static List<UltimatePreferenceItem<?>> createPreferences() {
		List<UltimatePreferenceItem<?>> prf = new ArrayList<>();
		prf.add(createLabel(
				"   ---   Octagon Domain   ---   "));
		prf.add(new UltimatePreferenceItem<WideningOperator>(
				WIDENING_OPERATOR,
				WIDENING_OPERATOR_DEFAULT, PreferenceType.Combo, WideningOperator.values()));
		prf.add(new UltimatePreferenceItem<String>(
				EXP_WIDENING_THRESHOLD,
				EXP_WIDENING_THRESHOLD_DEFAULT_VALUE, EXP_WIDENING_THRESHOLD_TOOLTIP, PreferenceType.String));
		return prf;
	}

	private static UltimatePreferenceItem<?> createLabel(String msg) {
		return new UltimatePreferenceItem<Object>(msg, null, PreferenceType.Label);
	}

}