/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Our Jordan-based loop acceleration works with closed forms of the variables
 * updates that are done in the loop. This class provides (static) methods that
 * construct these closed forms.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanAccelerationUtils {

	private JordanAccelerationUtils() {
		// do not instantiate
	}

	/**
	 * @return true iff -1 is an eigenvalue or for eigenvalue 1 there is a Jordan
	 *         block of size greater than 2.
	 */
	static boolean isAlternatingClosedFormRequired(final JordanUpdate jordanUpdate) {
		final boolean minus1isEigenvalue = jordanUpdate.getJordanBlockSizes().containsKey(-1);
		final boolean ev1hasBlockGreater2 = hasEv1JordanBlockStrictlyGreater2(jordanUpdate);
		return (minus1isEigenvalue || ev1hasBlockGreater2);
	}

	/**
	 * @return true iff there is some Jordan block for eigenvalue 1 whose size is
	 *         strictly greater than 2
	 */
	private static boolean hasEv1JordanBlockStrictlyGreater2(final JordanUpdate jordanUpdate) {
		boolean ev1hasBlockGreater2 = false;
		for (final int blockSize : jordanUpdate.getJordanBlockSizes().get(1).keySet()) {
			if (blockSize > 2 && (jordanUpdate.getJordanBlockSizes().get(1).get(blockSize) != 0)) {
				ev1hasBlockGreater2 = true;
			}
		}
		return ev1hasBlockGreater2;
	}

	static int computeSizeOfLargestEv0Block(final JordanUpdate jordanUpdate) {
		final NestedMap2<Integer, Integer, Integer> blockSizes = jordanUpdate.getJordanBlockSizes();
		if (!blockSizes.containsKey(0)) {
			return 0;
		} else {
			int max = 0;
			for (final int blockSize : jordanUpdate.getJordanBlockSizes().get(0).keySet()) {
				if (blockSize > max) {
					max = blockSize;
				}
			}
			assert max > 0;
			return max;
		}
	}

	/**
	 * The sum of the sizes of all block is the sum of the number of assigned scalar
	 * variables, the number of readonly variables and one (one is for the numbers
	 * that are added in the loop).
	 */
	static boolean isBlockSizeConsistent(final int numberOfAssignedVariables, final int numberOfReadonlyVariables,
			final JordanUpdate jordanUpdate) {
		int blockSizeSum = 0;
		for (final Triple<Integer, Integer, Integer> triple : jordanUpdate.getJordanBlockSizes().entrySet()) {
			blockSizeSum += triple.getSecond() * triple.getThird();
		}
		return (numberOfAssignedVariables + numberOfReadonlyVariables + 1 == blockSizeSum);
	}



	public static class LinearUpdate {
		Map<TermVariable, AffineTerm> mUpdateMap;
		Set<Term> mReadonlyVariables;

		public LinearUpdate(final Map<TermVariable, AffineTerm> updateMap, final Set<Term> readonlyVariables) {
			super();
			mUpdateMap = updateMap;
			mReadonlyVariables = readonlyVariables;
		}

		public Map<TermVariable, AffineTerm> getUpdateMap() {
			return mUpdateMap;
		}

		public Set<Term> getReadonlyVariables() {
			return mReadonlyVariables;
		}
	}
}
