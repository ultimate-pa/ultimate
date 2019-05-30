/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;

/**
 * Provides static auxiliary methods for {@link AffineTerm}s and
 * {@link PolynomialTerm}s
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolynomialTermUtils {

	private PolynomialTermUtils() {
		// do not instantiate
	}

	/**
	 * Use modulo operation to bring Rational in the range of representable values.
	 *
	 * @param bv
	 *            Rational that represents a bitvector
	 * @param sort
	 *            bitvector sort
	 * @return bv % 2^sort.getIndices[0]
	 */
	public static Rational bringValueInRange(final Rational bv, final Sort sort) {
		assert SmtSortUtils.isBitvecSort(sort);
		assert sort.getIndices().length == 1;
		assert bv.isIntegral();
		final int bitsize = sort.getIndices()[0].intValueExact();
		final BigInteger bvBigInt = bv.numerator();
		final BigInteger numberOfValues = BigInteger.valueOf(2).pow(bitsize);
		final BigInteger resultBigInt = BoogieUtils.euclideanMod(bvBigInt, numberOfValues);
		return Rational.valueOf(resultBigInt, BigInteger.ONE);
	}

	/**
	 * Generalized builder for sums of {@link AffineTerm}s and
	 * {@link PolynomialTerm}s. The type paramter T refers either to
	 * {@link AffineTerm} or {@link PolynomialTerm}. The type paramter V is a
	 * {@link Term} for {@link AffineTerm}s and a {@link Monomial} for
	 * {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<V,Rational>
	 *            map. (TODO: maybe we should make this map available via a package
	 *            private getter)
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	static <T extends IPolynomialTerm, V> T constructSum(final Function<IPolynomialTerm, Map<V, Rational>> term2map,
			final GeneralizedConstructor<V, T> constructor, final IPolynomialTerm... summands) {
		final Sort sort = summands[0].getSort();
		final Map<V, Rational> variable2Coefficient = new HashMap<>();
		Rational constant = Rational.ZERO;
		for (final IPolynomialTerm term : summands) {
			for (final Map.Entry<V, Rational> summand : term2map.apply(term).entrySet()) {
				// assert summand.getKey().getSort() == mSort : "Sort mismatch: " +
				// summand.getKey().getSort() + " vs. "
				// + mSort;
				final Rational coeff = variable2Coefficient.get(summand.getKey());
				if (coeff == null) {
					variable2Coefficient.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (SmtSortUtils.isBitvecSort(sort)) {
						newCoeff = bringValueInRange(coeff.add(summand.getValue()), sort);
					} else {
						newCoeff = coeff.add(summand.getValue());
					}
					if (newCoeff.equals(Rational.ZERO)) {
						variable2Coefficient.remove(summand.getKey());
					} else {
						variable2Coefficient.put(summand.getKey(), newCoeff);
					}
				}
			}
			if (SmtSortUtils.isBitvecSort(sort)) {
				constant = bringValueInRange(constant.add(term.getConstant()), sort);
			} else {
				constant = constant.add(term.getConstant());
			}
		}
		return constructor.apply(sort, constant, variable2Coefficient);
	}

	@FunctionalInterface
	interface GeneralizedConstructor<V, T> {
		public T apply(Sort sort, Rational constant, Map<V, Rational> map);
	}
}
