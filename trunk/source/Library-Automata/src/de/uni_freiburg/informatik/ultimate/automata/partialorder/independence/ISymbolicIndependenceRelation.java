/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.independence;

/**
 * Symbolic counterpart to conditional {@link IIndependenceRelation}s. Rather than deciding whether two actions commute
 * in a given context (described by a {@code CONDITION}), an instance of this interface generates a sufficient condition
 * for commutativity.
 *
 * @param <LETTER>
 *            The type of letters whose commutativity is considered
 * @param <CONDITION>
 *            The type of conditions that are generated
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public interface ISymbolicIndependenceRelation<LETTER, CONDITION> {
	/**
	 * Generates a sufficient condition under which the given letters commute, or returns {@code null} if no such
	 * condition could be found.
	 *
	 * @param existingCondition
	 *            Optionally, an existing condition which does not suffice for commutativity of the given letters. The
	 *            symbolic relation may take this condition into account and return a refined, more constraining
	 *            condition, but there is no guarantee that the returned condition is indeed a refinement of the
	 *            existing condition. If no condition is known or passing existing conditions is unsupported (see
	 *            {@link #isConditional()}), {@code null} may be used.
	 */
	CONDITION getCommutativityCondition(CONDITION existingCondition, LETTER a, LETTER b);

	/**
	 * Indicates whether this relation is symmetric (i.e., captures full commutativity) or not (i.e., captures
	 * semicommutativity, Lipton movers).
	 *
	 * @see IIndependenceRelation#isSymmetric()
	 */
	boolean isSymmetric();

	/**
	 * Indicates whether this relation can take advantage of a known existing condition (see
	 * {@link #getCommutativityCondition(CONDITION, LETTER, LETTER)}.
	 */
	boolean isConditional();
}
