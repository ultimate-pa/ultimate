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
	public static final String EXP_WIDENING_THRESHOLD_DEFAULT_VALUE = "65536"; // 2^16
	public static final String EXP_WIDENING_THRESHOLD_TOOLTIP
			= "Exponential widening will set values above this threshold to infinity";

	public static final String FALLBACK_ASSIGN_INTERVAL_PROJECTION = "Fallback: assign interval projection";
//	public static final String FALLBACK_ASSUME_LP_SOLVER = "Fallback: assume lp-solver";

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

		prf.add(new UltimatePreferenceItem<Boolean>(
				FALLBACK_ASSIGN_INTERVAL_PROJECTION, true, PreferenceType.Boolean));
//		prf.add(new UltimatePreferenceItem<Boolean>(
//				FALLBACK_ASSUME_LP_SOLVER, false, PreferenceType.Boolean));

		return prf;
	}

	private static UltimatePreferenceItem<?> createLabel(String msg) {
		return new UltimatePreferenceItem<Object>(msg, null, PreferenceType.Label);
	}

}