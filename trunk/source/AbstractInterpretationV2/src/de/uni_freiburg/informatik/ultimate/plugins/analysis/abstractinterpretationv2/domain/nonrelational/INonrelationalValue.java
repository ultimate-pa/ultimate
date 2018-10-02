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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ITermProvider;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <V>
 */
public interface INonrelationalValue<V extends INonrelationalValue<V>> extends ITermProvider {

	V copy();

	boolean isBottom();

	boolean isTop();

	V intersect(final V other);

	V merge(final V other);

	Collection<V> complement();

	Collection<V> complementInteger();

	/**
	 * Compares <code>this</code> with another value V for equality.
	 *
	 * @param other
	 *            The other value to compare to.
	 * @return <code>true</code> if and only if <code>this</code> and other are both bottom, <code>this</code> and other
	 *         are both top, or if the values represent the same abstract values.
	 */
	boolean isEqualTo(final V other);

	/**
	 * Compares <code>this</code> with another value V and checks whether <code>this</code> is included in other. If all
	 * values that are represented by this instance are represented by the other instance, return true. Return false
	 * otherwise.
	 *
	 * @param other
	 *            The other value to compare to.
	 * @return <code>true</code> if and only if <code>this</code> is included in other, <code>false</code> otherwise.
	 */
	boolean isContainedIn(final V other);

	V add(final V other);

	V subtract(final V other);

	V multiply(final V other);

	/**
	 * Negate this abstract value, i.e., perform unary minus.
	 *
	 * @return The negated abstract value.
	 */
	V negate();

	/**
	 * Compute the euclidean divison of dividend <code>this</code> with the divisor given as another value V of type
	 * integer.
	 *
	 * @param other
	 *            The divisor as another value V of type integer.
	 * @return A new value V of type integer that represents the result of the divison.
	 */
	V divideInteger(final V other);

	/**
	 * Compute the divison of dividend <code>this</code> with the divisor given as another value V of type real.
	 *
	 * @param other
	 *            The divisor as another value V of type real.
	 * @return A new value V of type real that represents the result of the divison.
	 */
	V divideReal(final V other);

	V modulo(final V other);

	V greaterThan(final V other);

	BooleanValue compareEquality(final V other);

	BooleanValue compareInequality(final V other);

	BooleanValue isGreaterThan(final V other);

	V greaterOrEqual(final V other);

	BooleanValue isGreaterOrEqual(final V other);

	V lessThan(final V other);

	BooleanValue isLessThan(final V other);

	V lessOrEqual(final V other);

	BooleanValue isLessOrEqual(final V other);

	V inverseModulo(final V referenceValue, final V oldValue, final boolean isLeft);

	V inverseEquality(final V oldValue, final V referenceValue);

	V inverseLessOrEqual(final V oldValue, final boolean isLeft);

	V inverseLessThan(final V oldValue, final boolean isLeft);

	V inverseGreaterOrEqual(final V oldValue, final boolean isLeft);

	V inverseGreaterThan(final V oldValue, final boolean isLeft);

	V inverseNotEqual(final V oldValue, final V referenceValue);

	boolean canHandleReals();

	boolean canHandleModulo();
}
