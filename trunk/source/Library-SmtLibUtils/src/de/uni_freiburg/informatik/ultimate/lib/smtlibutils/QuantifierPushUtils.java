/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.List;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Provides static methods that are utilized by the {@link QuantifierPushTermWalker}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPushUtils {

	/**
	 * If set to true we check after applying distributivity if we were able to eliminate some quantified variables. If
	 * elimination failed for all variables then we return the original term without applying distributivity.
	 *
	 */
	public static final boolean EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION = !true;
	public static final boolean ELIMINATEE_SEQUENTIALIZATION = true;
	public static final boolean DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION = true;


	static boolean isFlattened(final int quantifier, final List<Term> currentDualFiniteJuncts) {
		final Predicate<? super Term> notSameQuantifier = (x -> (QuantifierPusher.classify(quantifier,
				x) != FormulaClassification.SAME_QUANTIFIER));
		return currentDualFiniteJuncts.stream().allMatch(notSameQuantifier);
	}


}
