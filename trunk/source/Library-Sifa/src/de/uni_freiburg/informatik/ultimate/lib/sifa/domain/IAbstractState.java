/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;

/**
 * Interface for an abstract state that is used in {@link StateBasedDomain}
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of the state
 */
public interface IAbstractState<STATE extends IAbstractState<STATE>> extends ITermProvider {
	/**
	 * Joins two abstract states. The join of two abstract states is an over-approximation of their union.
	 *
	 * @param other
	 *            The state to be joined.
	 * @return An overapproximation of this ∪ other
	 */
	STATE join(STATE other);

	/**
	 * Widens one abstract state by another one.
	 * <p>
	 * Widening is similar to {@link #join} with the additional property that on any infinite sequence p1, p2, p3, ...
	 * the sequence w1, w2, w3, ... with w1 = p1 and wi = widen(w(i-1), pi) reaches a fixpoint, that is, wi = w(i+1) =
	 * w(i+2) = ... for some i.
	 *
	 * @param other
	 *            The state to be widened with
	 * @return A new widened state
	 */
	STATE widen(STATE other);

	/**
	 * Checks if this state represents bottom, i.e. represents the empty state.
	 *
	 * @return true iff this state is bottom
	 */
	boolean isBottom();
}
