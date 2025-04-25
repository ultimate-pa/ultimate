/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.math.BigInteger;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Test class for RationalMatrix.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class RationalMatrixTest {

	/**
	 * Tests the function {@link RationalMatrix#computeInverse(RationalMatrix)}.
	 */
	@Test
	public void testInverse() {
		// Identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		final RationalMatrix E_rational = new RationalMatrix(BigInteger.valueOf(1), E);
		final RationalMatrix E_inverse_computed = RationalMatrix.computeInverse(E_rational);
		QuadraticMatrixTest.checkBigIntegerEquality(BigInteger.valueOf(1), E_inverse_computed.getDenominator());
		QuadraticMatrixTest.checkMatrixEquality(E, E_inverse_computed.getIntMatrix());

		// Nontrivial matrix.
		final int[][] M1_entries = { { -1, 0, 3 }, { -1, 2, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M1 = QuadraticMatrixTest.intToBigInteger(M1_entries);
		final BigInteger denom1 = BigInteger.valueOf(2);
		final RationalMatrix R1 = new RationalMatrix(denom1, M1);
		final int[][] inverse1_entries = { { -2, 0, 6 }, { -1, 1, 1 }, { 0, 0, 2 } };
		final QuadraticMatrix M1_inverse = QuadraticMatrixTest.intToBigInteger(inverse1_entries);
		final RationalMatrix R1_inverse = new RationalMatrix(BigInteger.valueOf(1), M1_inverse);
		final RationalMatrix R1_inverse_computed = RationalMatrix.computeInverse(R1);
		QuadraticMatrixTest.checkBigIntegerEquality(BigInteger.valueOf(1), R1_inverse_computed.getDenominator());
		QuadraticMatrixTest.checkMatrixEquality(R1_inverse.getIntMatrix(), R1_inverse_computed.getIntMatrix());
	}

	/**
	 * Tests function {@link RationalMatrix#addColumnToMatrix(int, Rational[])}.
	 */
	@Test
	public void testAddColumnToMatrix() {
		// Tests the function addColumnToMatrix(int j, Rational[] p).
		final Rational[] p1 = new Rational[3];
		final Rational[] p2 = new Rational[3];
		final Rational[] p3 = new Rational[3];
		for (int i = 0; i < 3; i++) {
			p1[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
			p2[i] = Rational.valueOf(BigInteger.valueOf(i), BigInteger.valueOf(1));
			p3[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(i + 1));
		}
		final int[][] P1_entries = { { 6, 0, 6 }, { 6, 6, 3 }, { 6, 12, 2 } };
		final BigInteger denom1 = BigInteger.valueOf(6);
		final QuadraticMatrix P1 = QuadraticMatrixTest.intToBigInteger(P1_entries);
		final QuadraticMatrix P2_int = QuadraticMatrix.constructZeroMatrix(3);
		final RationalMatrix P2 = new RationalMatrix(BigInteger.valueOf(1), P2_int);
		P2.addColumnToMatrix(0, p1);
		P2.addColumnToMatrix(1, p2);
		P2.addColumnToMatrix(2, p3);
		QuadraticMatrixTest.checkBigIntegerEquality(denom1, P2.getDenominator());
		// assertEquals(denom, P2.mDenominator);
		QuadraticMatrixTest.checkMatrixEquality(P1, P2.getIntMatrix());

		final Rational[] p = new Rational[3];
		p[0] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
		p[1] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
		p[2] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
		final int[][] pEntriesOld = { { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 } };
		final QuadraticMatrix pOldInt = QuadraticMatrixTest.intToBigInteger(pEntriesOld);
		final int[][] pEntriesNew = { { 0, 1, 0 }, { 0, 0, 0 }, { 0, 0, 1 } };
		final QuadraticMatrix pNewInt = QuadraticMatrixTest.intToBigInteger(pEntriesNew);
		final BigInteger denom = BigInteger.valueOf(1);
		final RationalMatrix pOld = new RationalMatrix(denom, pOldInt);
		pOld.addColumnToMatrix(1, p);
		QuadraticMatrixTest.checkMatrixEquality(pOldInt, pNewInt);
		QuadraticMatrixTest.checkBigIntegerEquality(denom, pOld.getDenominator());
	}

	/**
	 * Tests function {@link RationalMatrix#addRowToMatrix(int, Rational[])}.
	 */
	@Test
	public void testAddRowToMatrix() {
		// Tests the function addColumnToMatrix(int j, Rational[] p).
		final Rational[] p1 = new Rational[3];
		final Rational[] p2 = new Rational[3];
		final Rational[] p3 = new Rational[3];
		for (int i = 0; i < 3; i++) {
			p1[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
			p2[i] = Rational.valueOf(BigInteger.valueOf(i), BigInteger.valueOf(1));
			p3[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(i + 1));
		}
		final int[][] P1_entries = { { 6, 6, 6 }, { 0, 6, 12 }, { 6, 3, 2 } };
		final BigInteger denom = BigInteger.valueOf(6);
		final QuadraticMatrix P1 = QuadraticMatrixTest.intToBigInteger(P1_entries);
		final QuadraticMatrix P2_int = QuadraticMatrix.constructZeroMatrix(3);
		final RationalMatrix P2 = new RationalMatrix(BigInteger.valueOf(1), P2_int);
		P2.addRowToMatrix(0, p1);
		P2.addRowToMatrix(1, p2);
		P2.addRowToMatrix(2, p3);
		QuadraticMatrixTest.checkBigIntegerEquality(denom, P2.getDenominator());
		// assertEquals(denom, P2.mDenominator);
		QuadraticMatrixTest.checkMatrixEquality(P1, P2.getIntMatrix());
	}
}
