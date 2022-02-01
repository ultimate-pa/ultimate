/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;

/**
 * Provides static auxiliary methods for {@link RefinementStrategy}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class RefinementStrategyUtils {

	private RefinementStrategyUtils() {
		// do not instantiate utility classes
	}

	/**
	 * @return true iff classified term does not contain {@link SmtUtils#FLOATINGPOINT_SORT}.
	 */
	public static boolean hasNoFloats(final TermClassifier tc) {
		return !tc.getOccuringSortNames().contains(SmtSortUtils.FLOATINGPOINT_SORT);
	}

	/**
	 * @return true iff classified term does not contain {@link SmtUtils#FP_TO_IEEE_BV_EXTENSION} and does not contain
	 *         quantifiers.
	 */
	public static boolean hasNoQuantifiersNoBitvectorExtensions(final TermClassifier tc) {
		return !tc.getOccuringFunctionNames().contains(SmtUtils.FP_TO_IEEE_BV_EXTENSION)
				&& tc.getOccuringQuantifiers().isEmpty();
	}

}
