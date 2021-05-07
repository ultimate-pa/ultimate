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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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
	public static Rational bringValueInRange(final Rational bv, final Sort sort) {
		assert SmtSortUtils.isBitvecSort(sort);
		assert sort.getIndices().length == 1;
		assert bv.isIntegral();
		final int bitsize = Integer.valueOf(sort.getIndices()[0]);
		final BigInteger bvBigInt = bv.numerator();
		final BigInteger numberOfValues = BigInteger.valueOf(2).pow(bitsize);
		final BigInteger resultBigInt = ArithmeticUtils.euclideanMod(bvBigInt, numberOfValues);
		return Rational.valueOf(resultBigInt, BigInteger.ONE);
	}

	/**
	 * Simplifies the given division as far as possible without changing the meaning
	 * of the term (i.e. divides as much of the division as possible, pulls out the
	 * latter constant (!= 0) divisors as coefficient if real-sort). Afterwards
	 * everything will be wrapped up in an AffineTerm as one variable.
	 */
	public static IPolynomialTerm simplifyImpossibleDivision(final String functionSymbol,
			final IPolynomialTerm[] polynomialArgs, final Script script) {
		final Term simplifiedVariable;
		final Rational coefficient;
		if (functionSymbol.equals("/")) {
			coefficient = constructCoefficient(polynomialArgs);
			simplifiedVariable = constructFutureVariableReal(polynomialArgs, script);
		} else if (functionSymbol.equals("div")) {
			coefficient = Rational.ONE;
			simplifiedVariable = constructFutureVariableInt(polynomialArgs, script);
		} else {
			throw new UnsupportedOperationException("Given type of division unknown.");
		}
		final AffineTerm wrappedVariable = AffineTerm.constructVariable(simplifiedVariable);
		return AffineTerm.mul(wrappedVariable, coefficient);
	}

	/**
	 * Return 1/(latter divisors which are constant and not 0). If there are no such
	 * divisors, return 1.
	 */
	private static Rational constructCoefficient(final IPolynomialTerm[] polynomialArgs) {
		Rational coeff = Rational.ONE;
		for (int i = polynomialArgs.length - 1; i >= 0; i--) {
			if (polynomialArgs[i].isConstant() && !polynomialArgs[i].getConstant().equals(Rational.ZERO)) {
				coeff = coeff.mul(polynomialArgs[i].getConstant());
			} else {
				break;
			}
		}
		return coeff.inverse();
	}

	/**
	 * Return an Array which represents the variable-part (everything but the
	 * coefficient, see "calculateCoefficient") of the given division, the arguments
	 * already in "pure" Term form (e.g. not a PolynomialTerm).
	 */
	private static Term constructFutureVariableReal(final IPolynomialTerm[] polynomialArgs, final Script script) {
		final IPolynomialTerm numerator = constructNumeratorReal(polynomialArgs, script);
		final int endOfVariableIncluded = calculateEndOfVariable(polynomialArgs);
		final int beginOfVariableIncluded = calculateBeginOfVariable(polynomialArgs);
		// Tell the method to include one more Element at the beginning, because that's
		// where we will insert the
		// new numerator.
		final Term[] variable = subArrayToTermSimplifyIntermediate(polynomialArgs, beginOfVariableIncluded - 1,
				endOfVariableIncluded, script);
		variable[0] = numerator.toTerm(script);
		return script.term("/", variable);
	}

	/**
	 * Returns the index at which a 0 or a variable occurs for the last time.
	 */
	private static int calculateEndOfVariable(final IPolynomialTerm[] polynomialArgs) {
		int endOfVariableIncluded = polynomialArgs.length - 1;
		boolean endOfVariableFound = false;
		for (; !endOfVariableFound; endOfVariableIncluded--) {
			endOfVariableFound = !polynomialArgs[endOfVariableIncluded].isConstant()
					|| polynomialArgs[endOfVariableIncluded].getConstant().equals(Rational.ZERO);
		}
		endOfVariableIncluded++;
		return endOfVariableIncluded;
	}

	/**
	 * Returns the index at which a 0 or a variable occurs for the first time
	 * (except for index 0).
	 */
	private static int calculateBeginOfVariable(final IPolynomialTerm[] polynomialArgs) {
		int beginOfVariableIncluded = 1;
		boolean beginOfVariableFound = false;
		for (; !beginOfVariableFound; beginOfVariableIncluded++) {
			beginOfVariableFound = !polynomialArgs[beginOfVariableIncluded].isConstant()
					|| polynomialArgs[beginOfVariableIncluded].getConstant().equals(Rational.ZERO);

		}
		beginOfVariableIncluded--;
		return beginOfVariableIncluded;
	}

	/**
	 * Does what the name suggests, except it does not simplify the very first 1.
	 */
	private static Term[] subArrayToTermSimplifyIntermediate(final IPolynomialTerm[] polynomialArgs,
			final int beginOfVariableIncluded, final int endOfSubArrayIncl, final Script script) {
		final ArrayList<Term> subList = new ArrayList<>();
		IPolynomialTerm simplifiedTerm = null;
		for (int i = beginOfVariableIncluded; i <= endOfSubArrayIncl; i++) {
			if (!polynomialArgs[i].isConstant() || polynomialArgs[i].getConstant().equals(Rational.ZERO)) {
				if (simplifiedTerm == null) {
					// don't add
				} else {
					subList.add(simplifiedTerm.toTerm(script));
					simplifiedTerm = null;
				}
				subList.add(polynomialArgs[i].toTerm(script));
			} else {
				if (polynomialArgs[i].isConstant() && polynomialArgs[i].getConstant().equals(Rational.ONE)) {
					// skip it, except it is the very first 1
					if (i == beginOfVariableIncluded) {
						subList.add(polynomialArgs[i].toTerm(script));
					}
				} else {
					if (simplifiedTerm == null) {
						simplifiedTerm = polynomialArgs[i];
					} else {
						simplifiedTerm = AffineTerm.mul(simplifiedTerm, polynomialArgs[i].getConstant());
					}
				}
			}
		}
		final Term[] subArray = new Term[subList.size()];
		subList.toArray(subArray);
		return subArray;
	}

	private static IPolynomialTerm constructNumeratorReal(final IPolynomialTerm[] divArray, final Script script) {
		final ArrayList<IPolynomialTerm> denominatorConstants = new ArrayList<>();
		boolean continueDivision = true;
		for (int i = 1; continueDivision && i < divArray.length; i++) {
			continueDivision = divArray[i].isConstant() && !divArray[i].isZero();
			if (continueDivision) {
				denominatorConstants.add(divArray[i]);
			}
		}
		if (denominatorConstants.isEmpty()) {
			return divArray[0];
		} else {
			return divideIPolynomialTermByConstants(divArray[0], denominatorConstants, script);
		}
	}

	private static IPolynomialTerm divideIPolynomialTermByConstants(final IPolynomialTerm numerator,
			final ArrayList<IPolynomialTerm> denomConstants, final Script script) {
		final IPolynomialTerm[] allConstants = new IPolynomialTerm[denomConstants.size() + 1];
		allConstants[0] = numerator;
		final Iterator<IPolynomialTerm> iter = denomConstants.iterator();
		for (int i = 1; iter.hasNext(); i++) {
			allConstants[i] = iter.next();
		}
		if (numerator.isAffine()) {
			return AffineTerm.divide(allConstants, script);
		} else {
			return PolynomialTerm.divide(allConstants, script);
		}
	}

	private static Term constructFutureVariableInt(final IPolynomialTerm[] polynomialArgs, final Script script) {
		final BiFunction<IPolynomialTerm[], Script, IPolynomialTerm> divider;
		if (polynomialArgs[0].isAffine()) {
			divider = AffineTerm::divide;
		} else {
			divider = PolynomialTerm::divide;
		}
		IPolynomialTerm newNumerator = polynomialArgs[0];
		final IPolynomialTerm[] binaryDivision = new IPolynomialTerm[2];
		binaryDivision[0] = polynomialArgs[0];
		int endOfSimplificationExcluded = 1;
		boolean stillSimplifiable = true;
		for (; stillSimplifiable
				&& endOfSimplificationExcluded < polynomialArgs.length; endOfSimplificationExcluded++) {
			if (polynomialArgs[endOfSimplificationExcluded].isConstant()
					&& !polynomialArgs[endOfSimplificationExcluded].isZero()) {
				binaryDivision[1] = polynomialArgs[endOfSimplificationExcluded];
				// Use the real Division here, because the int Division would return a single
				// Variable, if the quotient
				// would've been not integral, therefore we could not (properly) check for
				// integrality afterwards.
				newNumerator = divider.apply(binaryDivision, script);
				if (newNumerator.isIntegral()) {
					binaryDivision[0] = newNumerator;
				} else {
					newNumerator = binaryDivision[0];
					stillSimplifiable = false;
					endOfSimplificationExcluded--;
				}
			} else {
				stillSimplifiable = false;
				endOfSimplificationExcluded--;
			}
		}
		// Tell the method to include one more Element at the beginning, because that's
		// where we will insert the
		// new numerator.
		final Term[] variable = subArrayToTermSkipOnes(polynomialArgs, endOfSimplificationExcluded - 1,
				polynomialArgs.length - 1, script);
		variable[0] = newNumerator.toTerm(script);
		return script.term("div", variable);
	}

	/**
	 * Does what the name suggests, except it does not simplify the very first 1.
	 */
	private static Term[] subArrayToTermSkipOnes(final IPolynomialTerm[] polynomialArgs,
			final int beginOfVariableIncluded, final int endOfSubArrayIncl, final Script script) {
		final ArrayList<Term> subList = new ArrayList<>();
		for (int i = beginOfVariableIncluded; i <= endOfSubArrayIncl; i++) {
			if (polynomialArgs[i].isConstant() && polynomialArgs[i].getConstant().equals(Rational.ONE)) {
				// skip it, except it is the very first 1
				if (i == beginOfVariableIncluded) {
					subList.add(polynomialArgs[i].toTerm(script));
				}
			} else {
				subList.add(polynomialArgs[i].toTerm(script));
			}
		}
		final Term[] subArray = new Term[subList.size()];
		subList.toArray(subArray);
		return subArray;
	}

	/**
	 * Generalized method for applying Modulo to the coefficients and the constant
	 * of {@link AffineTerm}s and {@link PolynomialTerm}s. The type parameter T
	 * refers either to {@link AffineTerm} or {@link PolynomialTerm}. The type
	 * parameter MNL is a {@link Term} for {@link AffineTerm}s and a
	 * {@link Monomial} for {@link PolynomialTerm}s.
	 *
	 * @param term2map
	 *            {@link Function} that returns for a given T the Map<MNL,Rational>
	 *            map.
	 * @param constructor
	 *            Methods that constructs the term of type T.
	 */
	public static <T extends AbstractGeneralizedAffineTerm<MNL>, MNL> T applyModuloToAllCoefficients(
			final T agAffineTerm, final BigInteger divident, final GeneralizedConstructor<MNL, T> constructor) {
		assert SmtSortUtils.isIntSort(agAffineTerm.getSort());
		final SparseMapBuilder<MNL, Rational> mapBuilder = new SparseMapBuilder<>();
		Rational newCoeff;
		for (final Entry<MNL, Rational> entry : agAffineTerm.getAbstractVariable2Coefficient().entrySet()) {
			newCoeff = SmtUtils.toRational(ArithmeticUtils.euclideanMod(SmtUtils.toInt(entry.getValue()), divident));
			if (newCoeff != Rational.ZERO) {
				mapBuilder.put(entry.getKey(), newCoeff);
			}
		}
		final Rational constant = SmtUtils
				.toRational(ArithmeticUtils.euclideanMod(SmtUtils.toInt(agAffineTerm.getConstant()), divident));
		return constructor.apply(agAffineTerm.getSort(), constant, mapBuilder.getBuiltMap());
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
		Rational constant = Rational.ZERO;
		for (final IPolynomialTerm term : summands) {
			for (final Map.Entry<MNL, Rational> summand : term2map.apply(term).entrySet()) {
				// assert summand.getKey().getSort() == mSort : "Sort mismatch: " +
				// summand.getKey().getSort() + " vs. " + mSort;
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
	static <T extends IPolynomialTerm, MNL> T constructMul(
			final Function<IPolynomialTerm, Map<MNL, Rational>> term2map,
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
				if (divisor.equals(Rational.ONE) || SmtUtils.isBvMinusOne(divisor, sort)) {
					// We use multiplication instead of division
					// because we know that in this special case divisor is
					// always its own multiplicative inverse.
					result = PolynomialTermUtils.bringValueInRange(divident.mul(divisor), sort);
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
