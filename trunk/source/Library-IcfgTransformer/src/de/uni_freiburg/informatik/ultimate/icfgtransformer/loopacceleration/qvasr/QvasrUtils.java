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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * A collection of useful functions needed in Q-Vasr-abstraction, and matrix operations.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */
public class QvasrUtils {
	private QvasrUtils() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Split a {@link Term} in DNF into its conjuncts.
	 *
	 * @param loopRelation
	 * @return
	 */
	public static List<Term> splitDisjunction(final Term loopRelation) {
		final List<Term> result = new ArrayList<>();
		final ApplicationTerm dnfAppTerm = (ApplicationTerm) loopRelation;
		if (!dnfAppTerm.getFunction().getName().equals("or")) {
			result.add(loopRelation);
		} else {
			result.addAll(Arrays.asList(dnfAppTerm.getParameters()));
		}
		return result;
	}

	public static Rational[][] rationalMatrixMultiplication(final Rational[][] matrixOne,
			final Rational[][] matrixTwo) {
		final int rowMatrixOne = matrixOne[0].length;
		final int rowMatrixTwo = matrixTwo[0].length;
		final int colMatrixOne = matrixOne.length;
		final int colMatrixTwo = matrixTwo.length;
		if (rowMatrixTwo != colMatrixOne) {
			return new Rational[0][0];
		}
		final Rational[][] resultMatrix = new Rational[rowMatrixOne][colMatrixTwo];
		for (int i = 0; i < rowMatrixOne; i++) {
			for (int j = 0; j < colMatrixTwo; j++) {
				for (int k = 0; k < rowMatrixTwo; k++) {
					final Rational mul = matrixOne[i][k].mul(matrixTwo[k][j]);
					final Rational sum = resultMatrix[i][j].add(mul);
					resultMatrix[i][j] = sum;

				}
			}
		}
		return resultMatrix;
	}

	/**
	 * Embed a new variable into a set of subsets, by adding it to each already existing subsets.
	 *
	 * @param inSet
	 * @param variable
	 * @return
	 */
	public static Set<Set<Term>> joinSet(final Set<Set<Term>> inSet, final Set<Term> variable) {
		final Set<Set<Term>> joinedSet = new HashSet<>(inSet);
		for (final Set<Term> toBeJoined : inSet) {
			final Set<Term> varJoin = new HashSet<>();
			varJoin.addAll(toBeJoined);
			varJoin.addAll(variable);
			joinedSet.add(varJoin);
		}
		return joinedSet;
	}
}
