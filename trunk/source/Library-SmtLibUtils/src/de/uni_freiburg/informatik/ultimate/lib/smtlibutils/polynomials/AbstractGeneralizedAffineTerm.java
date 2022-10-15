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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
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
		assert !SmtSortUtils.isBitvecSort(s) || !constant.isNegative() : "Negative constant in bitvector term";
		assert !SmtSortUtils.isBitvecSort(s)
				|| allCoefficientsAreNonNegative(variables2coeffcient) : "Negative coefficients in bitvector term "
						+ variables2coeffcient;
		mAbstractVariable2Coefficient = variables2coeffcient;
	}

	private static boolean allCoefficientsAreNonNegative(final Map<?, Rational> variables2coeffcient) {
		return variables2coeffcient.entrySet().stream().allMatch(x -> !x.getValue().isNegative());
	}

	protected abstract IPolynomialTerm constructNew(final Sort sort, final Rational constant,
			final Map<AVAR, Rational> variables2coeffcient);

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
		final AbstractGeneralizedAffineTerm other = (AbstractGeneralizedAffineTerm) obj;
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

	public IPolynomialTerm div(final Script script, final BigInteger divisor, final Set<TermVariable> bannedForDivCapture) {
		if (!SmtSortUtils.isIntSort(getSort())) {
			throw new AssertionError("only for int");
		}
		final Map<AVAR, Rational> variables2coeffcient = new HashMap<>();
		final List<Term> summandsOfDiv = new ArrayList<>();
		for (final Entry<AVAR, Rational> entry : getAbstractVariable2Coefficient().entrySet()) {
			final Rational divisorAsRational = toRational(divisor);
			final Rational quotient = entry.getValue().div(divisorAsRational);
			if (quotient.isIntegral()) {
				final Rational euclideanQuotient = euclideanDivision(entry.getValue(), divisor);
				variables2coeffcient.put(entry.getKey(), euclideanQuotient);
			} else {
				if (getFreeVars(entry.getKey()).stream().anyMatch(bannedForDivCapture::contains)) {
					return null;
				}
				summandsOfDiv.add(SmtUtils.mul(script, entry.getValue(), abstractVariableToTerm(script, entry.getKey())));
			}
		}
		final Rational constant;
		if (summandsOfDiv.isEmpty()) {
			constant = euclideanDivision(getConstant(), divisor);
		} else {
			constant = Rational.ZERO;
			if (!getConstant().equals(Rational.ZERO)) {
				summandsOfDiv.add(getConstant().toTerm(getSort()));
			}
			final Term sum = SmtUtils.sum(script, getSort(), summandsOfDiv.toArray(new Term[summandsOfDiv.size()]));

			final Term div = SmtUtils.div(script, sum, SmtUtils.constructIntegerValue(script, getSort(), divisor));
			final AVAR avar = constructAbstractVar(div);
			final Rational oldCoeffcient = variables2coeffcient.put(avar, Rational.ONE);
			if (oldCoeffcient == null) {
				variables2coeffcient.put(avar, Rational.ONE);
			} else {
				final Rational newCoefficient = oldCoeffcient.add(Rational.ONE);
				variables2coeffcient.put(avar, newCoefficient);
			}
		}
		return constructNew(getSort(), constant, variables2coeffcient);
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
	public IPolynomialTerm add(final Rational offset) {
		final Rational newConstant;
		if (SmtSortUtils.isRealSort(getSort())) {
			newConstant = getConstant().add(offset);
		} else if (SmtSortUtils.isIntSort(getSort())) {
			newConstant = getConstant().add(offset);
		} else if (SmtSortUtils.isBitvecSort(getSort())) {
			newConstant = PolynomialTermUtils.bringBitvectorValueInRange(getConstant().add(offset), getSort());
		} else {
			throw new AssertionError("unsupported Sort " + getSort());
		}
		return constructNew(getSort(), newConstant, getAbstractVariable2Coefficient());
	}


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

		public ComparisonResult switchDiection() {
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
		final AbstractGeneralizedAffineTerm<?> lhsTerm = lhs.getPolynomialTerm();
		final AbstractGeneralizedAffineTerm<?> rhsTerm = rhs.getPolynomialTerm();
		if (!lhsTerm.getAbstractVariable2Coefficient().equals(rhsTerm.getAbstractVariable2Coefficient())) {
			throw new AssertionError("incomparable");
		}
		final RelationSymbol lhsRelationSymbol = lhs.getRelationSymbol();
		final RelationSymbol rhsRelationSymbol = rhs.getRelationSymbol();
		final Rational lhsConstant = lhs.getPolynomialTerm().getConstant();
		final Rational rhsConstant = rhs.getPolynomialTerm().getConstant();
		final ComparisonResult result = compare(lhsRelationSymbol, rhsRelationSymbol, lhsConstant, rhsConstant);
		assert doubleCheck(lhsRelationSymbol, rhsRelationSymbol, lhsConstant, rhsConstant,
				result) : "double check failed";
		return result;
	}

	private static boolean doubleCheck(final RelationSymbol lhsRelationSymbol, final RelationSymbol rhsRelationSymbol,
			final Rational lhsConstant, final Rational rhsConstant, final ComparisonResult result) {
		final ComparisonResult otherDirection = compare(rhsRelationSymbol, lhsRelationSymbol, rhsConstant, lhsConstant);
		if (result == null) {
			return (otherDirection == null);
		} else {
			return result.switchDiection().equals(otherDirection);
		}
	}

	/**
	 * Compare the relations lc lrel 0 and rc rrel 0
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

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Rational computeGcdOfCoefficients() {
		Rational gcd = Rational.ZERO;
		for (final Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
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