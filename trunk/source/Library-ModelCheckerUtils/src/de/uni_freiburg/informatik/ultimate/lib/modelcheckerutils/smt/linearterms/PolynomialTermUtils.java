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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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
	 * Constructs an iterated SMT-Term (func ...(func arg[0] arg[1]) ... arg[n]) as determined by the arguments.
	 */
	public static Term constructIteratedTerm(final String functionSymbol,
									         final IPolynomialTerm[] polynomialArgs,
											 final Script script) {

		Term term = script.term(functionSymbol, polynomialArgs[0].toTerm(script),
				   polynomialArgs[1].toTerm(script));
		for (int i = 2; i < polynomialArgs.length; i++) {
			term = script.term(functionSymbol, polynomialArgs[0].toTerm(script),
							          polynomialArgs[1].toTerm(script));
		}
		return term;
	}

	/**
	 * Generalized method for applying Modulo to the coefficients and the constant of
	 * {@link AffineTerm}s and {@link PolynomialTerm}s. The type parameter T refers either to
	 * {@link AffineTerm} or {@link PolynomialTerm}. The type parameter MNL is a
	 * {@link Term} for {@link AffineTerm}s and a {@link Monomial} for
	 * {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<MNL,Rational>
	 *            map.
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	public static <T extends AbstractGeneralizedAffineTerm<MNL>, MNL extends Term> T applyModuloToAllCoefficients(
			final T agAffineTerm, final BigInteger divident,
			final GeneralizedConstructor<MNL, T> constructor) {
		assert SmtSortUtils.isIntSort(agAffineTerm.getSort());
		final Map<MNL, Rational> newMap = new HashMap<>();
		Rational newCoeff;
		for (final Entry<MNL, Rational> entry : agAffineTerm.getAbstractVariable2Coefficient().entrySet()) {
			newCoeff = SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(entry.getValue()), divident));
			if (newCoeff == Rational.ZERO) {
				continue;
			} else {
				newMap.put(entry.getKey(), newCoeff);
			}
		}
		shrinkMap(newMap);
		final Rational constant = SmtUtils
				.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(agAffineTerm.getConstant()), divident));
		return constructor.apply(agAffineTerm.getSort(), constant, newMap);
	}

	/**
	 * Returns a shrinked version of a map if possible. Returns the given map otherwise.
	 */
	public static <MNL extends Term> Map<MNL, Rational> shrinkMap(final Map<MNL, Rational> map) {
		if (map.size() == 0) {
			return Collections.emptyMap();
		}
		else if (map.size() == 1) {
			final Entry<MNL, Rational> entry = map.entrySet().iterator().next();
			return Collections.singletonMap(entry.getKey(), entry.getValue());
		}
		return map;
	}

	/**
	 * It may occur, that the PolynomialTerm-class is used to represent a term, that could be represented by
	 * the AffineTerm-class. Hence, this method checks, whether the term given by the map could be represented by the
	 * AffineTerm-class.
	 */
	public static boolean isAffineMap(final Map<Monomial, Rational> map) {
		for(final Entry<Monomial, Rational> entry : map.entrySet()) {
			if (!entry.getKey().isLinear()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Convert a map in <Monomial, Rational> Form to an equivalent map in <Term, Rational> Form if possible.
	 */
	public static Map<Term, Rational> convertToAffineMap(final Map<Monomial, Rational> map){
		final Map<Term, Rational> affineMap = new HashMap<>();
		for(final Entry<Monomial, Rational> entry : map.entrySet()) {
			final Map<Term, Rational> monomialMap = entry.getKey().getVariable2Exponent();
			assert monomialMap.size() == 1 : "Cannot convert to AffineMap.";
			final Term term = monomialMap.keySet().iterator().next();
			affineMap.put(term, entry.getValue());
		}
		return shrinkMap(affineMap);
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
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	static <T extends AbstractGeneralizedAffineTerm<?>, MNL extends Term> T constructSum(
			final Function<IPolynomialTerm, Map<MNL, Rational>> term2map,
			final GeneralizedConstructor<MNL, T> constructor, final IPolynomialTerm... summands) {
		final Sort sort = summands[0].getSort();
		final Map<MNL, Rational> variable2Coefficient = new HashMap<>();
		Rational constant = Rational.ZERO;
		for (final IPolynomialTerm term : summands) {
			for (final Map.Entry<MNL, Rational> summand : term2map.apply(term).entrySet()) {
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

	/**
	 * Generalized builder for multiplication of a constant and either an
	 * {@link AffineTerm}s or a {@link PolynomialTerm}s. The type parameter T refers
	 * either to {@link AffineTerm} or {@link PolynomialTerm}. The type parameter MNL
	 * is a {@link Term} for {@link AffineTerm}s and a {@link Monomial} for
	 * {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<MNL,Rational>
	 *            map.
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	static <T extends IPolynomialTerm, MNL extends Term> T constructMul(
			final Function<IPolynomialTerm, Map<MNL, Rational>> term2map,
			final GeneralizedConstructor<MNL, T> constructor, final IPolynomialTerm term, final Rational multiplier) {
		final Sort sort;
		final Rational constant;
		final Map<MNL, Rational> variable2Coefficient;
		if (multiplier.equals(Rational.ZERO)) {
			sort = term.getSort();
			constant = Rational.ZERO;
			variable2Coefficient = Collections.emptyMap();
		} else {
			variable2Coefficient = new HashMap<>();
			sort = term.getSort();
			if (SmtSortUtils.isBitvecSort(sort)) {
				constant = PolynomialTermUtils.bringValueInRange(term.getConstant().mul(multiplier), sort);
			} else {
				assert sort.isNumericSort();
				constant = term.getConstant().mul(multiplier);
			}
			for (final Map.Entry<MNL, Rational> summand : term2map.apply(term).entrySet()) {
				variable2Coefficient.put(summand.getKey(), summand.getValue().mul(multiplier));
			}
		}
		return constructor.apply(sort, constant, variable2Coefficient);
	}

	@FunctionalInterface
	public interface GeneralizedConstructor<V, T> {
		public T apply(Sort sort, Rational constant, Map<V, Rational> map);
	}
}
