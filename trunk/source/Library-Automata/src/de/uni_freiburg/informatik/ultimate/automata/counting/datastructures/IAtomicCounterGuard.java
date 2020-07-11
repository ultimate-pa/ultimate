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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;

/**
 * Interface for relations between integer terms over counter variables.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IAtomicCounterGuard {

	/**
	 * Counter formula of the form c ◁ k such that c is a counter variable, ◁ ∈ { <,
	 * ⩽, >, ⩾, = }, and k ∈ ℕ.
	 */
	public static class SingleCounterGuard implements IAtomicCounterGuard {
		private final RelationSymbol mRelationSymbol;
		private final String mLhsCounter;
		private final BigInteger mRhsNaturalNumber;

		public SingleCounterGuard(final RelationSymbol relationSymbol, final String lhsCounter,
				final BigInteger rhsNaturalNumber) {
			super();
			Objects.nonNull(relationSymbol);
			Objects.nonNull(lhsCounter);
			Objects.nonNull(rhsNaturalNumber);
			mRelationSymbol = relationSymbol;
			mLhsCounter = lhsCounter;
			mRhsNaturalNumber = rhsNaturalNumber;
		}

		public RelationSymbol getRelationSymbol() {
			return mRelationSymbol;
		}

		public String getLhsCounter() {
			return mLhsCounter;
		}

		public BigInteger getRhsNaturalNumber() {
			return mRhsNaturalNumber;
		}

		@Override
		public String toString() {
			return String.format("(%s %s %s))", getRelationSymbol(), getLhsCounter(), getRhsNaturalNumber());
		}
	}

	/**
	 * Counter formula of the form t1 = t2, where t1 and t2 are arithmetic terms of
	 * the form c + k or k with k ∈ ℕ and c is counter variable. We use a
	 * representation where we have only one literal at the right-hand side and this
	 * literal can be an integer.
	 */
	public static class TermEqualityTest implements IAtomicCounterGuard {
		private final String mLhsCounter;
		private final String mRhsCounter;
		private final BigInteger mRhsNaturalNumber;

		public TermEqualityTest(final String lhsCounter, final String rhsCounter, final BigInteger rhsNaturalNumber) {
			super();
			Objects.requireNonNull(lhsCounter);
			Objects.requireNonNull(rhsCounter);
			Objects.requireNonNull(rhsNaturalNumber);
			mLhsCounter = lhsCounter;
			mRhsCounter = rhsCounter;
			mRhsNaturalNumber = rhsNaturalNumber;
		}

		public String getLhsCounter() {
			return mLhsCounter;
		}

		public String getRhsCounter() {
			return mRhsCounter;
		}

		public BigInteger getRhsNaturalNumber() {
			return mRhsNaturalNumber;
		}

		@Override
		public String toString() {
			if (getRhsNaturalNumber().compareTo(BigInteger.ZERO) >= 0) {
				return String.format("(= %s (+ %s %s))", getLhsCounter(), getRhsCounter(), getRhsNaturalNumber());
			} else {
				return String.format("(= (+ %s %s) %s )", getLhsCounter(), getRhsNaturalNumber().negate(),
						getRhsCounter());
			}
		}

	}
}