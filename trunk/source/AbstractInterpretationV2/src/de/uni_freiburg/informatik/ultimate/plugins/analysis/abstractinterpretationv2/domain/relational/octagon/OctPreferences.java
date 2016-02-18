package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

public class OctPreferences {

	public static enum WideningOperator {
		SIMPLE, EXPONENTIAL, LITERAL;
	}

	public static enum LogMessageFormatting {
		FULL_MATRIX, HALF_MATRIX, TERM;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static final String LOG_STRING_FORMAT = "Log string format";
	public static final LogMessageFormatting LOG_STRING_FORMAT_DEFAULT = LogMessageFormatting.HALF_MATRIX;

	public static final String WIDENING_OPERATOR = "Octagon widening operator";
	public static final WideningOperator WIDENING_OPERATOR_DEFAULT = WideningOperator.LITERAL;

	public static final String EXP_WIDENING_THRESHOLD = "Threshold for exponential widening";
	public static final String EXP_WIDENING_THRESHOLD_DEFAULT_VALUE = "131072"; // 2 * 2^16
	public static final String EXP_WIDENING_THRESHOLD_TOOLTIP
			= "Exponential widening will set matrix entries above this threshold to infinity. "
			+ "You may want to double the threshold, since interval bounds are stored with factor 2.";

	public static final String FALLBACK_ASSIGN_INTERVAL_PROJECTION = "Fallback: assign interval projection";
	public static final boolean FALLBACK_ASSIGN_INTERVAL_PROJECTION_DEFAULT = true;

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	public static List<UltimatePreferenceItem<?>> createPreferences() {

		List<UltimatePreferenceItem<?>> prf = new ArrayList<>();
		prf.add(makeLabel("   ---   Octagon Domain   ---   "));

		prf.add(new UltimatePreferenceItem<LogMessageFormatting>(LOG_STRING_FORMAT,
				LOG_STRING_FORMAT_DEFAULT, PreferenceType.Combo, LogMessageFormatting.values()));

		prf.add(new UltimatePreferenceItem<WideningOperator>(WIDENING_OPERATOR,
				WIDENING_OPERATOR_DEFAULT, PreferenceType.Combo, WideningOperator.values()));
		prf.add(new UltimatePreferenceItem<String>(EXP_WIDENING_THRESHOLD,
				EXP_WIDENING_THRESHOLD_DEFAULT_VALUE, EXP_WIDENING_THRESHOLD_TOOLTIP, PreferenceType.String));

		prf.add(new UltimatePreferenceItem<Boolean>(FALLBACK_ASSIGN_INTERVAL_PROJECTION,
				FALLBACK_ASSIGN_INTERVAL_PROJECTION_DEFAULT, PreferenceType.Boolean));

		return prf;
	}

	private static UltimatePreferenceItem<?> makeLabel(String msg) {
		return new UltimatePreferenceItem<Object>(msg, null, PreferenceType.Label);
	}

}