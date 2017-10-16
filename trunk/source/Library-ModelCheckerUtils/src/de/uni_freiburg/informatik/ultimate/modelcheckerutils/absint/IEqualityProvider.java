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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint;

/**
 * Interface to provide the equality provider for an abstract domain. The equality provider allows for checking whether
 * two variables of an abstract state are equal or not equal.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of the abstract states of this equality provider.
 * @param <VARDECL>
 *            The type of the variable declarations of this equality provider.
 * @param <EXPRESSION>
 *            The type of the expressions of this equality provider.
 */
public interface IEqualityProvider<STATE extends IAbstractState<STATE>, EXPRESSION> {

	/**
	 * Checks whether two expressions over a given abstract state are equal, i.e. whether they evaluate to the same
	 * value. Returns <code>true</code> if and only if the expressions are equal, <code>false</code> otherwise. Note
	 * that <code>false</code> does not imply that the expressions are not equal. <code>false</code> may also indicate
	 * "unknown".
	 *
	 * @param state
	 *            The abstract state.
	 * @param first
	 *            The first expression to check equality for.
	 * @param second
	 *            The second expression to check equality for.
	 * @return <code>true</code> if and only if the expressions are equal, <code>false</code> otherwise.
	 */
	boolean isDefinitelyEqual(final STATE state, final EXPRESSION first, final EXPRESSION second);

	/**
	 * Checks whether two expressions over a given abstract state are not equal, i.e. whether they do not evaluate to
	 * the same value. Returns <code>true</code> if and only if the expressions are not equal, <code>false</code>
	 * otherwise. Note that <code>false</code> does not imply that the expressions are not equal. <code>false</code> may
	 * also indicate "unknown".
	 *
	 * @param state
	 *            The abstract state.
	 * @param first
	 *            The first expression to check equality for.
	 * @param second
	 *            The second expression to check equality for.
	 * @return <code>true</code> if and only if the expressions are equal, <code>false</code> otherwise.
	 */
	boolean isDefinitelyNotEqual(final STATE state, final EXPRESSION first, final EXPRESSION second);
}
