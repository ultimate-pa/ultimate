/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.counting.datastructures;

import java.math.BigInteger;
import java.util.Objects;

/**
 * Represents assignments of the form
 * <ul>
 * <li>c := k and
 * <li>c := d + k,
 * </ul>
 * where c and d are counter and k is a natural number.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AtomicCounterAssingment {
	private final String mLhsCounter;
	private final String mRhsCounter;
	private final BigInteger mRhsNaturalNumber;

	/**
	 * @param rhsCounter
	 *            null iff there is no counter on the right-hand side.
	 */
	public AtomicCounterAssingment(final String lhsCounter, final String rhsCounter,
			final BigInteger rhsNaturalNumber) {
		super();
		Objects.nonNull(lhsCounter);
		if (rhsNaturalNumber.compareTo(BigInteger.ZERO) < 0) {
			throw new IllegalArgumentException("Literal in counter assignment mus be non-negative");
		}
		mLhsCounter = lhsCounter;
		mRhsCounter = rhsCounter;
		mRhsNaturalNumber = rhsNaturalNumber;
	}

	public String getLhsCounter() {
		return mLhsCounter;
	}

	/**
	 *
	 * @return The counter that is on the right-hand side of the assignment and null
	 *         if there is no counter on the right-hand side.
	 */
	public String getRhsCounter() {
		return mRhsCounter;
	}

	public BigInteger getRhsNaturalNumber() {
		return mRhsNaturalNumber;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getLhsCounter());
		sb.append(" := ");
		sb.append('"');
		if (mRhsCounter == null) {
			sb.append(getRhsNaturalNumber());
		} else {
			sb.append(String.format("(+ %s %s)", getRhsCounter(), getRhsNaturalNumber()));
		}
		sb.append('"');
		return sb.toString();
	}

}