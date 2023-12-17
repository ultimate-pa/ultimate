/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Generates conditions under which given transitions commute up to some independence relation.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public interface IIndependenceConditionGenerator {
	/**
	 * Generate a condition under which the given transitions are independent.
	 *
	 * @param context
	 *            A context that is already known, but not sufficient for commutativity
	 * @param a
	 *            The first transition
	 * @param b
	 *            The second transition
	 *
	 * @return a sufficient condition for independence
	 */
	IPredicate generateCondition(final IPredicate context, final UnmodifiableTransFormula a, final UnmodifiableTransFormula b);

	/**
	 * Generate a condition under which the given transitions are independent.
	 *
	 * @param a
	 *            The first transition
	 * @param b
	 *            The second transition
	 *
	 * @return a sufficient condition for independence
	 */
	default IPredicate generateCondition(final UnmodifiableTransFormula a, final UnmodifiableTransFormula b) {
		return generateCondition(null, a, b);
	}
}
