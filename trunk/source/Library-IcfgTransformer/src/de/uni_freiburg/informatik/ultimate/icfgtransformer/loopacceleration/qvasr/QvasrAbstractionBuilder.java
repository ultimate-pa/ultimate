/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Class for constructing a Qvasrabstraction using computed bases of resets and additions.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public final class QvasrAbstractionBuilder {
	private QvasrAbstractionBuilder() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Construct a new {@link QvasrAbstraction} (S, V) using an already computed simulation matrix, and an already
	 * existing qvasr.
	 *
	 * @param simulationMatrix
	 *            A {@link Rational} 2D-matrix representing a linear simulation.
	 * @param qvasr
	 *            A {@link Qvasr} representing the simulated set of transformers.
	 * @return A new {@link QvasrAbstraction}
	 */
	public static QvasrAbstraction constructQvasrAbstraction(final Rational[][] simulationMatrix, final Qvasr qvasr) {
		return new QvasrAbstraction(simulationMatrix, qvasr);
	}

	/**
	 * Construct a new {@link QvasrAbstraction} (S, V) using a vector basis for the resets and additions. By forming the
	 * {@link Qvasr} V and computing the corresponding simulation matrix S.
	 *
	 * @param resetsBasis
	 *            The vector space basis for the reset vector space.
	 * @param additionsBasis
	 *            The vector space basis for the addition vector space.
	 * @return A newly constructed {@link QvasrAbstraction}
	 */
	public static QvasrAbstraction constructQvasrAbstraction(final Rational[][] resetsBasis,
			final Rational[][] additionsBasis) {

		final int resetBasisSize = resetsBasis.length;
		final int additionBasisSize = additionsBasis.length;

		/*
		 * abstraction dimension d
		 */
		final int d = resetBasisSize + additionBasisSize;
		int n;
		/*
		 * Concrete dimension n
		 */
		if (resetBasisSize > additionBasisSize) {
			n = resetsBasis[0].length - 1;
		} else {
			n = additionsBasis[0].length - 1;
		}

		final Rational[][] simulationMatrix = new Rational[d][n];
		final Rational[] abstractionResetVector = new Rational[d];
		final Rational[] abstractionAdditionVector = new Rational[d];

		for (int i = 0; i < resetBasisSize; i++) {
			final Rational[] resetBasisVector = resetsBasis[i];
			simulationMatrix[i] = Arrays.copyOf(resetBasisVector, n);
			abstractionResetVector[i] = Rational.ZERO;
			abstractionAdditionVector[i] = resetBasisVector[resetBasisVector.length - 1];
		}
		for (int i = 0; i < additionBasisSize; i++) {
			final Rational[] additionsBasisVector = additionsBasis[i];
			simulationMatrix[i + resetBasisSize] = Arrays.copyOf(additionsBasisVector, n);
			abstractionResetVector[i + resetBasisSize] = Rational.ONE;
			abstractionAdditionVector[i + resetBasisSize] = additionsBasisVector[additionsBasisVector.length - 1];
		}
		final Qvasr qvasr = new Qvasr(abstractionResetVector, abstractionAdditionVector);
		return new QvasrAbstraction(simulationMatrix, qvasr);
	}
}
