/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;

/**
 * Preferences and default values for the Octagon abstract domain.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctagonDomainPreferences {

	public static enum WideningOperator {
		SIMPLE, EXPONENTIAL, LITERAL;
	}

	public static enum LogMessageFormatting {
		FULL_MATRIX, HALF_MATRIX, TERM;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static final String LOG_STRING_FORMAT = "Log string format";
	public static final LogMessageFormatting LOG_STRING_FORMAT_DEFAULT = LogMessageFormatting.TERM;

	public static final String WIDENING_OPERATOR = "Octagon widening operator";
	public static final WideningOperator WIDENING_OPERATOR_DEFAULT = WideningOperator.LITERAL;

	public static final String EXP_WIDENING_THRESHOLD = "Threshold for exponential widening";
	public static final String EXP_WIDENING_THRESHOLD_DEFAULT_VALUE = "131072"; // 2 * 2^16
	public static final String EXP_WIDENING_THRESHOLD_TOOLTIP =
			"Exponential widening will set matrix entries above this threshold to infinity. "
					+ "You may want to double the threshold, since interval bounds are stored with factor 2.";

	public static final String FALLBACK_ASSIGN_INTERVAL_PROJECTION = "Fallback: assign interval projection";
	public static final boolean FALLBACK_ASSIGN_INTERVAL_PROJECTION_DEFAULT = true;

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public static List<BaseUltimatePreferenceItem> createPreferences() {
		final List<BaseUltimatePreferenceItem> prf = new ArrayList<>();
		final UltimatePreferenceItemContainer octagonContainer = new UltimatePreferenceItemContainer("Octagon Domain");

		octagonContainer.addItem(new UltimatePreferenceItem<>(LOG_STRING_FORMAT, LOG_STRING_FORMAT_DEFAULT,
				PreferenceType.Combo, LogMessageFormatting.values()));

		octagonContainer.addItem(new UltimatePreferenceItem<>(WIDENING_OPERATOR, WIDENING_OPERATOR_DEFAULT,
				PreferenceType.Combo, WideningOperator.values()));
		octagonContainer.addItem(new UltimatePreferenceItem<>(EXP_WIDENING_THRESHOLD,
				EXP_WIDENING_THRESHOLD_DEFAULT_VALUE, EXP_WIDENING_THRESHOLD_TOOLTIP, PreferenceType.String));

		octagonContainer.addItem(new UltimatePreferenceItem<>(FALLBACK_ASSIGN_INTERVAL_PROJECTION,
				FALLBACK_ASSIGN_INTERVAL_PROJECTION_DEFAULT, PreferenceType.Boolean));

		prf.add(octagonContainer);
		return prf;
	}
}