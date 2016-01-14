/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;

/**
 * Defines the Ultimate preferences page for the interval domain and the kind of evaluators to use.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainPreferences {

	public static final String LABEL_INTERVAL_DOMAIN_SEPARATOR = "   ---   Interval Domain   ---   ";

	public static final String VALUE_WIDENING_OPERATOR_SIMPLE = IntervalSimpleWideningOperator.class.getSimpleName();
	public static final String VALUE_WIDENING_OPERATOR_LITERALS = IntervalLiteralWideningOperator.class.getSimpleName();
	public static final String[] VALUES_WIDENING_OPERATOR = new String[] { VALUE_WIDENING_OPERATOR_SIMPLE,
	        VALUE_WIDENING_OPERATOR_LITERALS };

	public static final String VALUE_EVALUATOR_DEFAULT = "Default Evaluator";
	public static final String VALUE_EVALUATOR_OPTIMIZATION = "Optimizer Evaluator";
	public static final String[] VALUES_EVALUATOR_TYPE = new String[] { VALUE_EVALUATOR_DEFAULT,
	        VALUE_EVALUATOR_OPTIMIZATION };

	public static final String LABEL_INTERVAL_WIDENING_OPERATOR = "Widening operator";

	public static final String LABEL_EVALUATOR_TYPE = "Evaluator type";

	// DEFAULT VALUES
	public static final String DEF_WIDENING_OPERATOR = VALUE_WIDENING_OPERATOR_SIMPLE;
	public static final String DEF_EVALUATOR_TYPE = VALUE_EVALUATOR_DEFAULT;

	public static List<UltimatePreferenceItem<?>> getPreferences() {

		final List<UltimatePreferenceItem<?>> returnList = new ArrayList<>();

		returnList.add(new UltimatePreferenceItem<String>(LABEL_INTERVAL_DOMAIN_SEPARATOR, null, PreferenceType.Label));

		returnList.add(new UltimatePreferenceItem<String>(LABEL_INTERVAL_WIDENING_OPERATOR, DEF_WIDENING_OPERATOR,
		        PreferenceType.Combo, VALUES_WIDENING_OPERATOR));

		returnList.add(new UltimatePreferenceItem<String>(LABEL_EVALUATOR_TYPE, DEF_EVALUATOR_TYPE,
		        PreferenceType.Combo, VALUES_EVALUATOR_TYPE));

		return returnList;
	}
}
