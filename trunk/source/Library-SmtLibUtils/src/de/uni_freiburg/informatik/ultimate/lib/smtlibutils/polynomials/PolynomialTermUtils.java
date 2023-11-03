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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SparseMapBuilder;

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
	public static Rational bringBitvectorValueInRange(final Rational bv, final Sort sort) {
		assert SmtSortUtils.isBitvecSort(sort);
		final int bitsize = SmtSortUtils.getBitvectorLength(sort);
		final BigInteger bvBigInt = bv.numerator();
		final BigInteger numberOfValues = BigInteger.valueOf(2).pow(bitsize);
		final BigInteger resultBigInt = ArithmeticUtils.euclideanMod(bvBigInt, numberOfValues);
		return Rational.valueOf(resultBigInt, BigInteger.ONE);
	}

	public static Rational bringValueInRange(final Rational rat, final Sort sort) {
		if (SmtSortUtils.isBitvecSort(sort)) {
			return bringBitvectorValueInRange(rat, sort);
		} else {
			return rat;
		}
	}

	/**
	 * It may occur, that the PolynomialTerm-class is used to represent a term, that
	 * could be represented by the AffineTerm-class. Hence, this method checks,
	 * whether the term given by the map could be represented by the
	 * AffineTerm-class.
	 */
	public static boolean isAffineMap(final Map<Monomial, Rational> map) {
		for (final Entry<Monomial, Rational> entry : map.entrySet()) {
			if (!entry.getKey().isLinear()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Convert a map in <Monomial, Rational> Form to an equivalent map in <Term,
	 * Rational> Form if possible.
	 */
	public static Map<Term, Rational> convertToAffineMap(final Map<Monomial, Rational> map) {
		final SparseMapBuilder<Term, Rational> mapBuilder = new SparseMapBuilder<>();
		for (final Entry<Monomial, Rational> entry : map.entrySet()) {
			final Map<Term, Rational> monomialMap = entry.getKey().getVariable2Exponent();
			assert monomialMap.size() == 1 : "Cannot convert to AffineMap.";
			final Term term = monomialMap.keySet().iterator().next();
			mapBuilder.put(term, entry.getValue());
		}
		return mapBuilder.getBuiltMap();
	}

	/**
	 * Generalized builder for sums of {@link AffineTerm}s and
	 * {@link PolynomialTerm}s. The type parameter T refers either to
	 * {@link AffineTerm} or {@link PolynomialTerm}. The type parameter MNL is a
	 * {@link Term} for {@link AffineTerm}s and a {@link Monomial} for
	 * {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<MNL,Rational>
	 *            map.
	 * @param wrapper
	 *            {
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	static <T extends AbstractGeneralizedAffineTerm<?>, MNL> T constructSum(
			final Function<IPolynomialTerm, Map<MNL, Rational>> term2map,
			final GeneralizedConstructor<MNL, T> constructor, final IPolynomialTerm... summands) {
		final Sort sort = summands[0].getSort();
		final Map<MNL, Rational> variable2Coefficient = new HashMap<>();
		Rational newConstant = Rational.ZERO;
		for (final IPolynomialTerm term : summands) {
			for (final Map.Entry<MNL, Rational> summand : term2map.apply(term).entrySet()) {
				// assert summand.getKey().getSort() == mSort : "Sort mismatch: " +
				// summand.getKey().getSort() + " vs. " + mSort;
				final Rational coeff = variable2Coefficient.get(summand.getKey());
				if (coeff == null) {
					variable2Coefficient.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff = bringValueInRange(coeff.add(summand.getValue()), sort);
					if (newCoeff.equals(Rational.ZERO)) {
						variable2Coefficient.remove(summand.getKey());
					} else {
						variable2Coefficient.put(summand.getKey(), newCoeff);
					}
				}
			}
			newConstant = bringValueInRange(newConstant.add(term.getConstant()), sort);
		}
		return constructor.apply(sort, newConstant, variable2Coefficient);
	}

	/**
	 * Generalized builder for multiplication of a constant and either an
	 * {@link AffineTerm}s or a {@link PolynomialTerm}s. The type parameter T refers
	 * either to {@link AffineTerm} or {@link PolynomialTerm}. The type parameter
	 * MNL is a {@link Term} for {@link AffineTerm}s and a {@link Monomial} for
	 * {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<MNL,Rational>
	 *            map.
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	static <T extends IPolynomialTerm, MNL> T constructMul(final Function<IPolynomialTerm, Map<MNL, Rational>> term2map,
			final GeneralizedConstructor<MNL, T> constructor, final IPolynomialTerm term, final Rational multiplier) {
		final Sort sort;
		final Rational constant;
		final Map<MNL, Rational> variable2Coefficient;
		if (multiplier.equals(Rational.ZERO)) {
			sort = term.getSort();
			constant = Rational.ZERO;
			variable2Coefficient = Collections.emptyMap();
		} else if (multiplier.equals(Rational.ONE)) {
			sort = term.getSort();
			constant = term.getConstant();
			variable2Coefficient = term2map.apply(term);
		} else {
			variable2Coefficient = new HashMap<>();
			sort = term.getSort();
			constant = PolynomialTermUtils.bringValueInRange(term.getConstant().mul(multiplier), sort);
			for (final Map.Entry<MNL, Rational> summand : term2map.apply(term).entrySet()) {
				final Rational newCoefficient = PolynomialTermUtils
						.bringValueInRange(summand.getValue().mul(multiplier), sort);
				variable2Coefficient.put(summand.getKey(), newCoefficient);
			}
		}
		return constructor.apply(sort, constant, variable2Coefficient);
	}

	@FunctionalInterface
	public interface GeneralizedConstructor<V, T> {
		public T apply(Sort sort, Rational constant, Map<V, Rational> map);
	}

	@FunctionalInterface
	public interface TriFunction<T, U, R, S> {
		public S apply(T script, U sort, R term);
	}


	/**
	 * Divide the given divident by the given divisor. Return the result only if for
	 * the given sort there is some "inverse" element invrs such that a
	 * multiplication of the result with invrs is equivalent to the divident. Return
	 * null if no such inverse element exists. We assume that for reals the division
	 * is "/" for ints the division is "div" and for bitvectors the division is
	 * "bvudiv".
	 */
	public static Rational divInvertible(final Sort sort, final Rational divident, final Rational divisor) {
		final Rational result;
		if (divisor.equals(Rational.ZERO)) {
			result = null;
		} else {
			if (SmtSortUtils.isRealSort(sort)) {
				final Rational quot = divident.div(divisor);
				result = quot;
			} else if (SmtSortUtils.isIntSort(sort)) {
				final Rational quot = divident.div(divisor);
				if (quot.isIntegral()) {
					result = quot;
				} else {
					result = null;
				}
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				if (divisor.equals(Rational.ONE) || SmtUtils.isBvMinusOneButNotOne(divisor, sort)) {
					// We use multiplication instead of division
					// because we know that in this special case divisor is
					// always its own multiplicative inverse.
					result = PolynomialTermUtils.bringBitvectorValueInRange(divident.mul(divisor), sort);
				} else {
					result = null;
				}
			} else {
				throw new AssertionError("unsupported sort");
			}
		}
		return result;
	}
}
