/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Layla Franke
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.parallel;

/**
 * A tuple class for integers.
 * @author Layla Franke
 */
public final class Tuple {
	/**
	 * The first integer.
	 */
	public final int mFirst;
	/**
	 * The second integer.
	 */
	public final int mSecond;

	/**
	 * Constructor.
	 * 
	 * @param first
	 *            first state
	 * @param second
	 *            second state
	 */
	public Tuple(final int first, final int second) {
		assert (first < second) : "The first entry must be the smaller one";
		mFirst = first;
		mSecond = second;
	}

	@Override
	public int hashCode() {
		return mFirst + 17 * mSecond;
	}

	@Override
	public boolean equals(final Object other) {
		if (!(other instanceof Tuple)) {
			return false;
		}
		final Tuple o = (Tuple) other;
		return (o.mFirst == mFirst) && (o.mSecond == mSecond);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("(");
		builder.append(mFirst);
		builder.append(", ");
		builder.append(mSecond);
		builder.append(")");
		return builder.toString();
	}
}
