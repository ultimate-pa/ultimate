/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;

/**
 * Represents a thread identifier (TID) as an immutable sequence of integers.
 *
 * <p>
 * A {@code Tid} is internally stored as an {@code Integer[]} and provides a string representation of the form
 * {@code tid_<i1>_<i2>_...}.
 * </p>
 *
 * <p>
 * This class is used in the ULTIMATE Civlizer plug-in to represent identifiers extracted from Boogie AST expressions.
 * </p>
 *
 * <p>
 * Equality and hash code are defined based on the underlying integer sequence.
 * </p>
 */
final class Tid {
	final private Integer[] mValue;
	final private String mRepresentation;

	Tid(final Integer[] value) {
		mValue = value;
		mRepresentation = Tid.getRepresentation(value);
	}

	Tid(final Expression[] expressions) {
		this(Arrays.stream(expressions).map(x -> {
			if (!(x instanceof IntegerLiteral)) {
				// not allow TODO Throw error
			}

			return Integer.parseInt(((IntegerLiteral) x).getValue());
		}).toArray(Integer[]::new));
	}

	static String getRepresentation(final Integer[] value) {

		final StringBuilder sb = new StringBuilder("tid");

		for (final Integer i : value) {
			sb.append("_").append(i);
		}

		return sb.toString();
	}

	Integer[] getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		return mRepresentation;
	}

	@Override
	public boolean equals(final Object o) {
		return Arrays.equals(mValue, ((Tid) o).mValue);
	}

	@Override
	public int hashCode() {
		return Arrays.hashCode(mValue);
	}
}