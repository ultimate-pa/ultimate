/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SparseMapBuilder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Common superclass of {@link AffineTerm} and {@link PolynomialTerm}. This class represents an affine term whose kinds
 * of variables are abstract objectsspecified by a type parameter. For a {@link PolynomialTerm} these abstract variables
 * are {@link Monomials} for an {@link AffineTerm} the instance of these abstract variables are already "the variables".
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <AVAR>
 *            type of the variables
 */
public abstract class AbstractGeneralizedAffineTerm<AVAR> extends Term implements IPolynomialTerm {

	public enum Equivalence { EQUALS, DISTINCT, INCOMPARABLE };

	/**
	 * Map from abstract variables to coeffcients. Coefficient zero is forbidden.
	 */
	protected final Map<AVAR, Rational> mAbstractVariable2Coefficient;
	/**
	 * Affine constant (the coefficient without variable).
	 */
	protected final Rational mConstant;
	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	protected final Sort mSort;

	/**
	 * Auxiliary {@link AbstractGeneralizedAffineTerm} term that represents an error during the translation process,
	 * e.g., if original term was not linear or not polynomial.
	 */
	public AbstractGeneralizedAffineTerm() {
		super(0);
		mAbstractVariable2Coefficient = null;
		mConstant = null;
		mSort = null;
	}

	/**
	 * Default constructor for non-error terms.
	 */
	protected AbstractGeneralizedAffineTerm(final Sort s, final Rational constant,
			final Map<AVAR, Rational> variables2coeffcient) {
		super(0);
		Objects.requireNonNull(s);
		Objects.requireNonNull(constant);
		Objects.requireNonNull(variables2coeffcient);
		mSort = s;
		mConstant = constant;
		assert !SmtSortUtils.isBitvecSort(s) || !constant.isNegative() : "Negative constant in BitVec term";
		assert !SmtSortUtils.isBitvecSort(s) || isTrueForAllCoefficients(variables2coeffcient,
				x -> !x.isNegative()) : "Negative coefficient in BitVec term " + variables2coeffcient;
		assert !SmtSortUtils.isBitvecSort(s) || constant.isIntegral() : "Non-integral constant in BitVec term";
		assert !SmtSortUtils.isBitvecSort(s) || isTrueForAllCoefficients(variables2coeffcient,
				x -> x.isIntegral()) : "Non-integral coefficient in BitVec term " + variables2coeffcient;
		assert !SmtSortUtils.isIntSort(s) || constant.isIntegral() : "Non-integral constant in Int term";
		assert !SmtSortUtils.isIntSort(s) || isTrueForAllCoefficients(variables2coeffcient,
				x -> x.isIntegral()) : "Non-integral coefficient in Int term " + variables2coeffcient;
		mAbstractVariable2Coefficient = variables2coeffcient;
	}

	private static boolean isTrueForAllCoefficients(final Map<?, Rational> variable2coeffcient, final Predicate<Rational> p) {
		return variable2coeffcient.entrySet().stream().allMatch(x -> p.test(x.getValue()));
	}

	protected abstract AbstractGeneralizedAffineTerm<?> constructNew(final Sort sort, final Rational constant,
			final Map<AVAR, Rational> variables2coeffcient);

	/**
	 * Construct a new {@link AffineTerm} in which term is the only variable. This
	 * is usually a bad idea and useful only in rare cases. Hence, this method is
	 * private.
	 */
	private static AffineTerm constructNewSingleVariableTerm(final Term term) {
		return new AffineTerm(term.getSort(), Rational.ZERO, Collections.singletonMap(term, Rational.ONE));
	}

	protected abstract AVAR constructAbstractVar(Term term);

	protected abstract Collection<Term> getFreeVars(AVAR var);

	/**
	 * True if this represents not an legal term of its kind but an error during the translation process, e.g., if
	 * original term was not linear or not polynomial.
	 */
	@Override
	public boolean isErrorTerm() {
		if (mAbstractVariable2Coefficient == null) {
			assert mConstant == null;
			assert mSort == null;
			return true;
		} else {
			assert mConstant != null;
			assert mSort != null;
			return false;
		}
	}

	/*
	 * check documentation of subclasses
	 */
	public abstract boolean isVariable(Term var);

	/**
	 * @return whether this {@link AbstractGeneralizedAffineTerm} is just a constant
	 */
	@Override
	public boolean isConstant() {
		return mAbstractVariable2Coefficient.isEmpty();
	}

	/**
	 * @return whether this {@link AbstractGeneralizedAffineTerm} is zero
	 */
	@Override
	public boolean isZero() {
		return mConstant.equals(Rational.ZERO) && mAbstractVariable2Coefficient.isEmpty();
	}

	/**
	 * Check whether every coefficient and every constant is of an integral value. Return true if thats the case.
	 */
	@Override
	public boolean isIntegral() {
		if (!getConstant().isIntegral()) {
			return false;
		}
		for (final Rational coefficient : getAbstractVariable2Coefficient().values()) {
			if (!coefficient.isIntegral()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @return the constant summand of this {@link AbstractGeneralizedAffineTerm}
	 */
	@Override
	public Rational getConstant() {
		return mConstant;
	}

	/**
	 * Check if term is of a type that may be a variable of an {@link AbstractGeneralizedAffineTerm}.
	 */
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of AffineTerm has to be TermVariable or ApplicationTerm");
		}
	}

	/**
	 *
	 * @return A {@link Monomial} in which subject is a variable and no other
	 *         variable of the {@link Monomial} contains subject as a subterm and no
	 *         other monomial contains the subject. If no such monomial exists we
	 *         return null
	 */
	Monomial getExclusiveMonomialOfSubject(final Term subject) {
		Monomial result = null;
		for (final AVAR abstractVar : getAbstractVariable2Coefficient().keySet()) {
			if (abstractVar instanceof Monomial) {
				final Monomial monomial = (Monomial) abstractVar;
				switch (monomial.isExclusiveVariable(subject)) {
				case AS_EXCLUSIVE_VARIABlE:
					if (result != null) {
						// not exclusive
						return null;
					} else {
						result = monomial;
					}
					break;
				case NON_EXCLUSIVE_OR_SUBTERM:
					return null;
				case NOT:
					break;
				default:
					throw new AssertionError("illegal value");
				}
			} else {
				if (subject.equals(abstractVar)) {
					if (result != null) {
						// not exclusive
						return null;
					} else {
						result = new Monomial(subject, Rational.ONE);
					}
				} else {
					final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
							.isSatisfiedBySomeSubterm((Term) abstractVar);
					if (subjectOccursAsSubterm) {
						return null;
					}
				}
			}
		}
		return result;
	}




	@Override
	public String toString() {
		if (isErrorTerm()) {
			return "auxilliaryErrorTerm";
		}
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!mConstant.equals(Rational.ZERO) || sb.length() == 0) {
			if (mConstant.isNegative() || sb.length() > 0) {
				sb.append(mConstant.isNegative() ? " - " : " + ");
			}
			sb.append(mConstant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}

		return result;
	}

	/**
	 * @return an SMT {@link Term} that represents an abstract variable that occurs in the map of this object
	 */
	protected abstract Term abstractVariableToTerm(Script script, AVAR abstractVariable);

	/**
	 * @return an SMT {@link Term} that represents an abstract variable that occurs in the map of this object TIMES the given coefficient.
	 */
	protected abstract Term abstractVariableTimesCoeffToTerm(Script script, AVAR abstractVariable, Rational coeff);

	/**
	 * Transforms this {@link AbstractGeneralizedAffineTerm} into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	@Override
	public Term toTerm(final Script script) {
		Term[] summands;
		if (mConstant.equals(Rational.ZERO)) {
			summands = new Term[mAbstractVariable2Coefficient.size()];
		} else {
			summands = new Term[mAbstractVariable2Coefficient.size() + 1];
		}
		int i = 0;
		for (final Map.Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal coefficient in AffineTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = abstractVariableToTerm(script, entry.getKey());
			} else {
				summands[i] = abstractVariableTimesCoeffToTerm(script, entry.getKey(), entry.getValue());
			}
			++i;
		}
		if (!mConstant.equals(Rational.ZERO)) {
			assert mConstant.isIntegral() || SmtSortUtils.isRealSort(mSort);
			summands[i] = SmtUtils.rational2Term(script, mConstant, mSort);
		}
		final Term result = SmtUtils.sum(script, mSort, summands);
		return result;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	Map<AVAR, Rational> getAbstractVariable2Coefficient() {
		return Collections.unmodifiableMap(mAbstractVariable2Coefficient);
	}

	public Map<Term, Rational> getAbstractVariableAsTerm2Coefficient(final Script script) {
		final HashMap<Term, Rational> result = new HashMap<>();
		for (final Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			result.put(abstractVariableToTerm(script, entry.getKey()), entry.getValue());
		}
		return result;
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + (mConstant == null ? 0 : mConstant.hashCode());
		result = prime * result + (mSort == null ? 0 : mSort.hashCode());
		result = prime * result
				+ (mAbstractVariable2Coefficient == null ? 0 : mAbstractVariable2Coefficient.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final AbstractGeneralizedAffineTerm<?> other = (AbstractGeneralizedAffineTerm<?>) obj;
		if (mConstant == null) {
			if (other.mConstant != null) {
				return false;
			}
		} else if (!mConstant.equals(other.mConstant)) {
			return false;
		}
		if (mSort == null) {
			if (other.mSort != null) {
				return false;
			}
		} else if (!mSort.equals(other.mSort)) {
			return false;
		}
		if (mAbstractVariable2Coefficient == null) {
			if (other.mAbstractVariable2Coefficient != null) {
				return false;
			}
		} else if (!mAbstractVariable2Coefficient.equals(other.mAbstractVariable2Coefficient)) {
			return false;
		}
		return true;
	}

	protected abstract Pair<Rational, Rational> computeMinMax();


	/**
	 * @return absolut value of divisor if term is modulo term, null otherwise
	 */
	protected Rational checkForModTerm(final Term term) {
		final ApplicationTerm appTerm = SmtUtils.getFunctionApplication(term, "mod");
		if (appTerm == null) {
			return null;
		}
		final Term divisorAsTerm = appTerm.getParameters()[1];
		final Rational divisorAsRational = SmtUtils.tryToConvertToLiteral(divisorAsTerm);
		if (divisorAsRational == null) {
			return null;
		} else {
			return divisorAsRational.abs();
		}
	}

	public abstract AbstractGeneralizedAffineTerm<?> removeAndNegate(Monomial monomialOfSubject);

	private ApplicationTerm isDivision(final String funcname) {
		if (!mConstant.equals(Rational.ZERO)) {
			return null;
		}
		if (mAbstractVariable2Coefficient.size() != 1) {
			return null;
		}
		final Entry<AVAR, Rational> entry = mAbstractVariable2Coefficient.entrySet().iterator().next();
		if (!entry.getValue().equals(Rational.ONE)) {
			return null;
		}
		final AVAR avar = entry.getKey();
		final Term singleVar;
		if (avar instanceof Monomial) {
			final Monomial monominal = (Monomial) avar;
			singleVar = monominal.getSingleVariable();
		} else if (avar instanceof Term) {
			singleVar = (Term) avar;
		} else {
			throw new AssertionError();
		}
		if (!(singleVar instanceof ApplicationTerm)) {
			return null;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) singleVar;
		if (!appTerm.getFunction().getApplicationString().equals(funcname)) {
			return null;
		}
		return appTerm;
	}

	@Override
	public IPolynomialTerm div(final Script script, final IPolynomialTerm... divisors) {
		AbstractGeneralizedAffineTerm<?> current = this;
		for (final IPolynomialTerm divisor : divisors) {
			if (divisor.isConstant()) {
				if (SmtSortUtils.isIntSort(mSort)) {
					current = current.divInt(script, divisor.getConstant().numerator(), Collections.emptySet());
				} else if (SmtSortUtils.isBitvecSort(mSort)) {
					throw new UnsupportedOperationException(
							"Cannot apply div (meant for integers) to term whose sort is bitvector.");
				} else if (SmtSortUtils.isRealSort(mSort)) {
					current = current.divReal(script, divisor.getConstant());
				} else {
					throw new UnsupportedOperationException();
				}
			} else {
				final String funcname = getDivisionFuncname(getSort());
				// TODO: extract gcd from divisor and divide by gcd separately
				current = constructDivResultForNonSimplifiableCase(script, funcname, current, divisor.toTerm(script));
			}
		}
		return current;
	}

	public static String getDivisionFuncname(final Sort sort) {
		final String funcname;
		if (SmtSortUtils.isIntSort(sort)) {
			funcname = "div";
		} else if (SmtSortUtils.isBitvecSort(sort)) {
			throw new UnsupportedOperationException();
		} else if (SmtSortUtils.isRealSort(sort)) {
			funcname = "/";
		} else {
			throw new UnsupportedOperationException();
		}
		return funcname;
	}

	/**
	 * If divisor is zero (for Int and for Real, not for bitvector) or not a
	 * literal, we cannot simplify besides flattening and return an
	 * {@link AffineTerm} whose only variable is the divisibility result.
	 *
	 */
	private static AffineTerm constructDivResultForNonSimplifiableCase(final Script script, final String funcname,
			final IPolynomialTerm divident, final Term divisor) {
		return constructNewSingleVariableTerm(
				SmtUtils.flattenIntoFirstArgument(script, funcname, divident.toTerm(script), divisor));
	}

	public AbstractGeneralizedAffineTerm<?> divInt(final Script script, final BigInteger divisor,
			final Set<TermVariable> bannedForDivCapture) {
		if (!SmtSortUtils.isIntSort(getSort())) {
			throw new AssertionError("only for int");
		}
		if (divisor.equals(BigInteger.ZERO)) {
			// A non-initial zero cannot be simplified (semantics of division by zero
			// similar to uninterpreted function see
			// http://smtlib.cs.uiowa.edu/theories-Ints.shtml). This means especially that
			// an initial zero does not make the result zero, because 0 is not equivalent to
			// (div 0 0).
			return constructDivResultForNonSimplifiableCase(script, "div", this,
					SmtUtils.constructIntegerValue(script, getSort(), divisor));
		}
		// Idea: Pull all summand whose coefficient is a multiple of the divisor out of
		// the `div`.
		final Map<AVAR, Rational> divisible = new HashMap<>();
		final Map<AVAR, Rational> nonDivisible = new HashMap<>();
		final Rational divisorAsRational = toRational(divisor);
		for (final Entry<AVAR, Rational> entry : getAbstractVariable2Coefficient().entrySet()) {
			final Rational quotient = entry.getValue().div(divisorAsRational);
			if (quotient.isIntegral()) {
				final Rational euclideanQuotient = euclideanDivision(entry.getValue(), divisor);
				divisible.put(entry.getKey(), euclideanQuotient);
			} else {
				if (getFreeVars(entry.getKey()).stream().anyMatch(bannedForDivCapture::contains)) {
					return null;
				}
				nonDivisible.put(entry.getKey(), entry.getValue());
			}
		}
		// The constant of the result. Will be zero if we cannot pull the input's
		// constant out of the `div`.
		final Rational constant;
		if (nonDivisible.isEmpty()) {
			// since all coefficients could be divided without remainder, it is sound to
			// divide the constant even if it is not divisible without remainder
			constant = euclideanDivision(getConstant(), divisor);
		} else {
			// The constant that stays inside the `div`. Will be zero if we can pull the
			// input's constant out of the `div`.
			final Rational constantOfDivArgument;
			if (getConstant().div(Rational.valueOf(divisor, BigInteger.ONE)).isIntegral()) {
				// constant can be divided without remainder
				constant = euclideanDivision(getConstant(), divisor);
				constantOfDivArgument = Rational.ZERO;
			} else {
				// constant cannot be divided without remainder, we have to add the constant to
				// the sum (to which we apply the div operator)
				constant = Rational.ZERO;
				constantOfDivArgument = getConstant();
			}
			final Pair<Rational, Term> coeffAndDiv = divIntHelper(script, nonDivisible, constantOfDivArgument,
					divisorAsRational);
			// Add `div` term to resulting polynomial. Take care of the special case that
			// the resulting polynomial already has a variable that is coincides with the
			// div Term.
			final AVAR avar = constructAbstractVar(coeffAndDiv.getSecond());
			final Rational oldCoeffcient = divisible.get(avar);
			if (oldCoeffcient == null) {
				divisible.put(avar, coeffAndDiv.getFirst());
			} else {
				final Rational newCoefficient = oldCoeffcient.add(coeffAndDiv.getFirst());
				if (newCoefficient.equals(Rational.ZERO)) {
					divisible.remove(avar);
				} else {
					divisible.put(avar, newCoefficient);
				}
			}
		}
		return constructNew(getSort(), constant, divisible);
	}

	/**
	 * Construct polynomial and apply `div` with two simplifications.
	 * <li>Divide polynomial and divisor by the GCD of all coefficients, the
	 * constant, and the divisor.
	 * <li>Make the divisor positive. If it was negative the `div` term's
	 * coefficient will be `-1`.
	 *
	 * @param coefficientToVar Map whose coefficients are NOT divisible by the
	 *                         divisor.
	 * @param constant         Number that is not divisible by the divisor.
	 */
	private Pair<Rational, Term> divIntHelper(final Script script, final Map<AVAR, Rational> coefficientToVar,
			final Rational constant, final Rational divisor) {
		AbstractGeneralizedAffineTerm<?> divArgument = constructNew(getSort(), constant, coefficientToVar);
		final Rational gcd = divArgument.computeGcdOfCoefficientsAndConstant().gcd(divisor).abs();
		if (!gcd.equals(Rational.ONE)) {
			divArgument = divArgument.divInvertible(gcd);
		}
		final Term divArgumentAsTerm = divArgument.toTerm(script);
		final Rational newDivisor = divisor.div(gcd).abs();
		assert newDivisor.isIntegral();
		final Term resultDivTerm = SmtUtils.divIntFlatten(script, divArgumentAsTerm, newDivisor.numerator());
		final Rational resultCoefficient = divisor.isNegative() ? Rational.MONE : Rational.ONE;
		return new Pair<>(resultCoefficient, resultDivTerm);
	}


	public AbstractGeneralizedAffineTerm<?> divReal(final Script script, final Rational divisor) {
		if (!SmtSortUtils.isRealSort(getSort())) {
			throw new AssertionError("only for Real");
		}
		if (divisor.equals(Rational.ZERO)) {
			return constructDivResultForNonSimplifiableCase(script, "/", this, divisor.toTerm(getSort()));
		}
		return (AbstractGeneralizedAffineTerm<?>) this.mul(divisor.inverse());
	}

	protected Rational euclideanDivision(final Rational divident, final BigInteger divisor) {
		if (!divident.isIntegral()) {
			throw new AssertionError();
		}
		return toRational(ArithmeticUtils.euclideanDiv(divident.numerator(), divisor));
	}

	private static Rational toRational(final BigInteger bi) {
		return Rational.valueOf(bi, BigInteger.ONE);
	}

	@Override
	public abstract AbstractGeneralizedAffineTerm<?> divInvertible(Rational r);

	@Override
	public IPolynomialTerm mod(final Script script, final IPolynomialTerm divisor) {
		if (divisor.isConstant()) {
			return mod(script, divisor.getConstant().numerator());
		} else {
			return constructNewSingleVariableTerm(script.term("mod", this.toTerm(script), divisor.toTerm(script)));
		}
	}

	public IPolynomialTerm mod(final Script script, final BigInteger divisor) {
		if (divisor.equals(BigInteger.ZERO)) {
			final Term resultAsTerm = script.term("mod", this.toTerm(script),
					SmtUtils.constructIntegerValue(script, getSort(), divisor));
			return constructNewSingleVariableTerm(resultAsTerm);
		}
		final Map<AVAR, Rational> preprocessedMap = modPreprocessMap(script, divisor.abs());
		final Rational preprocessedConstant = SmtUtils
				.toRational(ArithmeticUtils.euclideanMod(SmtUtils.toInt(getConstant()), divisor.abs()));
		final AbstractGeneralizedAffineTerm<?> intermediateResult = constructNew(getSort(), preprocessedConstant,
				preprocessedMap);
		if (preprocessedMap.isEmpty()) {
			// Result is a constant. Effect of the modulo was already taken into account
			return intermediateResult;
		}
		final Pair<Rational, Rational> minmax = intermediateResult.computeMinMax();
		if (minmax != null && !minmax.getFirst().isNegative()
				&& minmax.getSecond().compareTo(Rational.valueOf(divisor, BigInteger.ONE)) < 0) {
			// outer modulo is useless, we are in range [0 ... divisor) anyway.
			return intermediateResult;
		}
		final Rational gcd = computeGcdOfValues(preprocessedMap).gcd(preprocessedConstant)
				.gcd(Rational.valueOf(divisor, BigInteger.ONE));
		assert !gcd.isNegative() && !gcd.equals(Rational.ZERO);
		if (gcd.equals(Rational.ONE)) {
			// No further simplification possible. Return AffineTerm whose single variable
			// is
			// the modulo term.
			final Term intermediateResultAsTerm = script.term("mod", intermediateResult.toTerm(script),
					SmtUtils.constructIntegerValue(script, getSort(), divisor.abs()));
			return constructNewSingleVariableTerm(intermediateResultAsTerm);
		} else {
			// GCD is > 1. We pull out the GCD (divide coeff+const and divisor by GCD,
			// multiply result by GCD).
			final AbstractGeneralizedAffineTerm<?> quotientPoly = intermediateResult
					.divInvertible(gcd);
			final BigInteger quotientDivisor = divisor.abs().divide(gcd.numerator());
			// Call method recursively because the new divisor might enable further
			// simplifications in the polynomial
			final IPolynomialTerm recResult = quotientPoly.mod(script, quotientDivisor);
			return recResult.mul(gcd);
		}
	}

	/**
	 * Apply two transformations the variable map of an affine term.
	 * <li>If the variable has the form `(mod t k)` and k is divisible by `divisor`
	 * we replace the variable by `t`
	 * <li>We apply modulo to all coefficients.
	 */
	private Map<AVAR, Rational> modPreprocessMap(final Script script, final BigInteger divisor) {
		assert divisor.compareTo(BigInteger.ZERO) > 0 : "Divisor must be positive";
		final SparseMapBuilder<AVAR, Rational> smb = new SparseMapBuilder<>();
		for (final Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			final Rational newCoefficient = SmtUtils
					.toRational(ArithmeticUtils.euclideanMod(SmtUtils.toInt(entry.getValue()), divisor));
			if (newCoefficient.equals(Rational.ZERO)) {
				continue;
			}
			final AVAR newAvar = constructAbstractVarForModulo(script, entry.getKey(), divisor);
			// Changing a variable may require a merge of two map entries via addition of
			// the coefficients
			if (smb.containsKey(newAvar)) {
				final Rational oldEntry = smb.get(newAvar);
				final Rational sumTmp = oldEntry.add(entry.getValue());
				// An addition of coefficients requires that we apply the modulo operation
				// again.
				final Rational sum = SmtUtils.toRational(ArithmeticUtils.euclideanMod(SmtUtils.toInt(sumTmp), divisor));
				if (sum.equals(Rational.ZERO)) {
					smb.remove(newAvar);
				} else {
					smb.put(newAvar, sum);
				}
			} else {
				smb.put(newAvar, newCoefficient);
			}
		}
		return smb.getBuiltMap();
	}

	/**
	 * Prepare abstract variable for an application of `mod`. In case the abstract
	 * variable is itself a `mod` term and its divisor is divisible by the divisor
	 * of our `mod` application, we can omit the inner `mod`. <br>
	 * E.g., `(mod (mod x 32) 4)` is (mod x 4).
	 */
	private AVAR constructAbstractVarForModulo(final Script script, final AVAR abstractVar, final BigInteger divisor) {
		final ApplicationTerm appTerm = SmtUtils.getFunctionApplication(abstractVariableToTerm(script, abstractVar),
				"mod");
		if (appTerm == null) {
			return abstractVar;
		}
		assert appTerm.getParameters().length == 2;
		final Term innerDivisorTerm = appTerm.getParameters()[1];
		final Rational innerDivisorRational = SmtUtils.tryToConvertToLiteral(innerDivisorTerm);
		if (innerDivisorRational == null) {
			return abstractVar;
		}
		if (innerDivisorRational.div(Rational.valueOf(divisor, BigInteger.ONE)).isIntegral()) {
			// inner divisor is divisible by outer divisor
			final Term divident = appTerm.getParameters()[0];
			return constructAbstractVar(divident);
		} else {
			return abstractVar;
		}
	}

	@Override
	public abstract AbstractGeneralizedAffineTerm<AVAR> add(final Rational offset);

	@Override
	public Equivalence compare(final IPolynomialTerm otherTerm) {
		final Equivalence result;
		if (otherTerm instanceof AbstractGeneralizedAffineTerm) {
			final AbstractGeneralizedAffineTerm<?> otherPoly = (AbstractGeneralizedAffineTerm<?>) otherTerm;
			if (this.getAbstractVariable2Coefficient().equals(otherPoly.getAbstractVariable2Coefficient())) {
				if (this.getConstant().equals(otherPoly.getConstant())) {
					result = Equivalence.EQUALS;
				} else {
					result = Equivalence.DISTINCT;
				}
			} else {
				result = Equivalence.INCOMPARABLE;
			}
		} else {
			result = Equivalence.INCOMPARABLE;
		}
		return result;
	}


	public enum ComparisonResult {
		INCONSISTENT, IMPLIES, EXPLIES, EQUIVALENT;

		public ComparisonResult switchDirection() {
			final ComparisonResult result;
			switch (this) {
			case EQUIVALENT:
				result = this;
				break;
			case EXPLIES:
				result = IMPLIES;
				break;
			case IMPLIES:
				result = EXPLIES;
				break;
			case INCONSISTENT:
				result = this;
				break;
			default:
				throw new AssertionError("unknown value " + this);
			}
			return result;
		}
	}

	public static ComparisonResult compareRepresentation(final PolynomialRelation lhs, final PolynomialRelation rhs) {
		if (!lhs.getPolynomialTerm().getSort().equals(rhs.getPolynomialTerm().getSort())) {
			throw new AssertionError("Cannot compare polynomials of different sorts");
		}
		final AbstractGeneralizedAffineTerm<?> lhsTerm = lhs.getPolynomialTerm();
		final AbstractGeneralizedAffineTerm<?> rhsTerm = rhs.getPolynomialTerm();
		if (!lhsTerm.getAbstractVariable2Coefficient().equals(rhsTerm.getAbstractVariable2Coefficient())) {
			throw new AssertionError("incomparable");
		}
		final RelationSymbol lhsRelationSymbol;
		final RelationSymbol rhsRelationSymbol;
		final Rational lhsConstant;
		final Rational rhsConstant;
		if (SmtSortUtils.isIntSort(lhs.getPolynomialTerm().getSort())) {
			lhsRelationSymbol = lhs.getRelationSymbol().getCorrespondingNonStrictRelationSymbol();
			rhsRelationSymbol = rhs.getRelationSymbol().getCorrespondingNonStrictRelationSymbol();
			lhsConstant = lhs.getPolynomialTerm().getConstant()
					.add(lhs.getRelationSymbol().getOffsetForStrictToNonstrictTransformation());
			rhsConstant = rhs.getPolynomialTerm().getConstant()
					.add(rhs.getRelationSymbol().getOffsetForStrictToNonstrictTransformation());
		} else {
			lhsRelationSymbol = lhs.getRelationSymbol();
			rhsRelationSymbol = rhs.getRelationSymbol();
			lhsConstant = lhs.getPolynomialTerm().getConstant();
			rhsConstant = rhs.getPolynomialTerm().getConstant();
		}
		final ComparisonResult result = compare(lhsRelationSymbol, rhsRelationSymbol, lhsConstant, rhsConstant);
		assert doubleCheck(lhsRelationSymbol, rhsRelationSymbol, lhsConstant, rhsConstant, result)
				: "double check failed";
		return result;
	}

	private static boolean doubleCheck(final RelationSymbol lhsRelationSymbol, final RelationSymbol rhsRelationSymbol,
			final Rational lhsConstant, final Rational rhsConstant, final ComparisonResult result) {
		final ComparisonResult otherDirection = compare(rhsRelationSymbol, lhsRelationSymbol, rhsConstant, lhsConstant);
		if (result == null) {
			return (otherDirection == null);
		} else {
			return result.switchDirection().equals(otherDirection);
		}
	}

	/**
	 * Compare the relations lc lrel 0 and rc rrel 0.
	 *
	 * Consider lc and rc as rationals, so that e.g., c > 0 and c >=1 are not
	 * considered equivalent.
	 */
	private static ComparisonResult compare(final RelationSymbol lhsRelationSymbol,
			final RelationSymbol rhsRelationSymbol, final Rational lhsConstant, final Rational rhsConstant)
			throws AssertionError {
		final ComparisonResult result;
		switch (lhsRelationSymbol) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			result = compareDistinct(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		case EQ:
			result = compareEq(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		case GEQ:
			result = compareGeq(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		case GREATER:
			result = compareGreater(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		case LEQ:
			result = compareLeq(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		case LESS:
			result = compareLess(lhsConstant, rhsRelationSymbol, rhsConstant);
			break;
		default:
			throw new AssertionError("unknown value: " + lhsRelationSymbol);
		}
		return result;
	}

	/**
	 * Compare the relations lc neq 0 and rc rrel 0
	 */
	public static ComparisonResult compareDistinct(final Rational lhsConstant, final RelationSymbol relationSymbol,
			final Rational rhsConstant) {
		final ComparisonResult result;
		switch (relationSymbol) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lhsConstant.equals(rhsConstant)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = null;
			}
			break;
		case EQ:
			if (lhsConstant.equals(rhsConstant)) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.EXPLIES;
			}
			break;
		case GEQ:
			if (lhsConstant.compareTo(rhsConstant) > 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = null;
			}
			break;
		case GREATER:
			if (lhsConstant.compareTo(rhsConstant) >= 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = null;
			}

			break;
		case LEQ:
			if (lhsConstant.compareTo(rhsConstant) < 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = null;
			}
			break;
		case LESS:
			if (lhsConstant.compareTo(rhsConstant) <= 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = null;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + relationSymbol);
		}
		return result;
	}

	/**
	 * Compare the relations lc = 0 and rc rrel 0
	 */
	public static ComparisonResult compareEq(final Rational lc, final RelationSymbol rRel, final Rational rc) {
		final ComparisonResult result;
		switch (rRel) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lc.equals(rc)) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case EQ:
			if (lc.equals(rc)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = ComparisonResult.INCONSISTENT;
			}
			break;
		case GEQ:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case GREATER:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LEQ:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LESS:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + rRel);
		}
		return result;
	}

	/**
	 * Compare the relations lc >= 0 and rc rrel 0
	 */
	public static ComparisonResult compareGeq(final Rational lc, final RelationSymbol rRel, final Rational rc) {
		final ComparisonResult result;
		switch (rRel) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.IMPLIES;
			} else {
				result = null;
			}
			break;
		case EQ:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.EXPLIES;
			}
			break;
		case GEQ:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.EXPLIES;
			} else if (lc.equals(rc)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case GREATER:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LEQ:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case LESS:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + rRel);
		}
		return result;
	}

	/**
	 * Compare the relations lc > 0 and rc rrel 0
	 */
	public static ComparisonResult compareGreater(final Rational lc, final RelationSymbol rRel, final Rational rc) {
		final ComparisonResult result;
		switch (rRel) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.IMPLIES;
			} else {
				result = null;
			}
			break;
		case EQ:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.EXPLIES;
			}
			break;
		case GEQ:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case GREATER:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.EXPLIES;
			} else if (lc.equals(rc)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LEQ:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case LESS:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + rRel);
		}
		return result;
	}

	/**
	 * Compare the relations lc <= 0 and rc rrel 0
	 */
	public static ComparisonResult compareLeq(final Rational lc, final RelationSymbol rRel, final Rational rc) {
		final ComparisonResult result;
		switch (rRel) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.IMPLIES;
			} else {
				result = null;
			}
			break;
		case EQ:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.EXPLIES;
			}
			break;
		case GEQ:
			if (lc.compareTo(rc) > 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case GREATER:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case LEQ:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.EXPLIES;
			} else if (lc.equals(rc)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LESS:
			if (lc.compareTo(rc) <= 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + rRel);
		}
		return result;
	}

	/**
	 * Compare the relations lc < 0 and rc rrel 0
	 */
	public static ComparisonResult compareLess(final Rational lc, final RelationSymbol rRel, final Rational rc) {
		final ComparisonResult result;
		switch (rRel) {
		case BVSGE:
		case BVSGT:
		case BVSLE:
		case BVSLT:
		case BVUGE:
		case BVUGT:
		case BVULE:
		case BVULT:
			throw new AssertionError("not in PolynomialRelation");
		case DISTINCT:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.IMPLIES;
			} else {
				result = null;
			}
			break;
		case EQ:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = ComparisonResult.EXPLIES;
			}
			break;
		case GEQ:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case GREATER:
			if (lc.compareTo(rc) >= 0) {
				result = ComparisonResult.INCONSISTENT;
			} else {
				result = null;
			}
			break;
		case LEQ:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.EXPLIES;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		case LESS:
			if (lc.compareTo(rc) < 0) {
				result = ComparisonResult.EXPLIES;
			} else if (lc.equals(rc)) {
				result = ComparisonResult.EQUIVALENT;
			} else {
				result = ComparisonResult.IMPLIES;
			}
			break;
		default:
			throw new AssertionError("unknown value: " + rRel);
		}
		return result;
	}


	public static boolean areRepresentationsFusible(final Junction junction, final PolynomialRelation lhs,
			final PolynomialRelation rhs) {
		if (!lhs.getPolynomialTerm().getSort().equals(rhs.getPolynomialTerm().getSort())) {
			throw new AssertionError("Cannot compare polynomials of different sorts");
		}
		final AbstractGeneralizedAffineTerm<?> lhsTerm = lhs.getPolynomialTerm();
		final AbstractGeneralizedAffineTerm<?> rhsTerm = rhs.getPolynomialTerm();
		if (!lhsTerm.getAbstractVariable2Coefficient().equals(rhsTerm.getAbstractVariable2Coefficient())) {
			throw new AssertionError("incomparable");
		}
		if (!lhs.getRelationSymbol().isConvexInequality() && !rhs.getRelationSymbol().isConvexInequality()) {
			return false;
		}
		final RelationSymbol lhsRelationSymbol;
		final RelationSymbol rhsRelationSymbol;
		final Rational lhsConstant;
		final Rational rhsConstant;
		if (SmtSortUtils.isIntSort(lhs.getPolynomialTerm().getSort())) {
			lhsRelationSymbol = lhs.getRelationSymbol().getCorrespondingNonStrictRelationSymbol();
			rhsRelationSymbol = rhs.getRelationSymbol().getCorrespondingNonStrictRelationSymbol();
			lhsConstant = lhs.getPolynomialTerm().getConstant()
					.add(lhs.getRelationSymbol().getOffsetForStrictToNonstrictTransformation());
			rhsConstant = rhs.getPolynomialTerm().getConstant()
					.add(rhs.getRelationSymbol().getOffsetForStrictToNonstrictTransformation());
		} else {
			lhsRelationSymbol = lhs.getRelationSymbol();
			rhsRelationSymbol = rhs.getRelationSymbol();
			lhsConstant = lhs.getPolynomialTerm().getConstant();
			rhsConstant = rhs.getPolynomialTerm().getConstant();
		}
		return areRepresentationsFusibleHelper(junction, lhsRelationSymbol, rhsRelationSymbol, lhsConstant,
				rhsConstant);
	}

	/**
	 */
	private static boolean areRepresentationsFusibleHelper(final Junction junction,
			final RelationSymbol lhsRelationSymbol, final RelationSymbol rhsRelationSymbol, final Rational lhsConstant,
			final Rational rhsConstant) {
		if (!lhsRelationSymbol.isConvexInequality() || !rhsRelationSymbol.isConvexInequality()) {
			return false;
		}
		switch (junction) {
		case AND:
			if (lhsRelationSymbol.equals(RelationSymbol.LEQ) && rhsRelationSymbol.equals(RelationSymbol.GEQ)
					|| lhsRelationSymbol.equals(RelationSymbol.GEQ) && rhsRelationSymbol.equals(RelationSymbol.LEQ)) {
				if (rhsConstant.equals(lhsConstant)) {
					return true;
				}
			}
			return false;
		case OR:
			if (lhsRelationSymbol.equals(RelationSymbol.LESS) && rhsRelationSymbol.equals(RelationSymbol.GREATER)
					|| lhsRelationSymbol.equals(RelationSymbol.GREATER)
							&& rhsRelationSymbol.equals(RelationSymbol.LESS)) {
				if (rhsConstant.equals(lhsConstant)) {
					return true;
				}
			}
			return false;
		default:
			throw new AssertionError();

		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Rational computeGcdOfCoefficients() {
		final Map<?, Rational> map = mAbstractVariable2Coefficient;
		return computeGcdOfValues(map);
	}


	public Rational computeGcdOfCoefficientsAndConstant() {
		return computeGcdOfCoefficients().gcd(getConstant());
	}

	private static Rational computeGcdOfValues(final Map<?, Rational> map) {
		Rational gcd = Rational.ZERO;
		for (final Entry<?, Rational> entry : map.entrySet()) {
			gcd = gcd.gcd(entry.getValue());
		}
		return gcd;
	}

	@Override
	public TermVariable[] getFreeVars() {
		throw new UnsupportedOperationException(
				"AbstractGeneralizedAffineTerm is not a proper Term of our SMT library");
	}

	@Override
	public Theory getTheory() {
		throw new UnsupportedOperationException(
				"AbstractGeneralizedAffineTerm is not a proper Term of our SMT library");
	}

	@Override
	public String toStringDirect() {
		throw new UnsupportedOperationException(
				"AbstractGeneralizedAffineTerm is not a proper Term of our SMT library");
	}
}