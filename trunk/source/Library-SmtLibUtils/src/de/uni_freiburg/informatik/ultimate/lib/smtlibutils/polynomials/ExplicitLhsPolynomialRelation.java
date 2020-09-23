/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.Arrays;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.IBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Polynomial relation in which we explicitly state which {@link Monomial}
 * (together with its coefficient) is on the left-hand side. This class is used
 * as an intermediate data structure by algorithms that try to solve a
 * polynomial relation for a given subject.
 *
 * <pre>
 * Work in progress.
 * * Maybe we want to allow more general right-hand sides.
 * * Maybe we do not only want to solve relations (coefficient one) but
 *     want to do transformations whose result has a specific coefficient.
 * </pre>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ExplicitLhsPolynomialRelation implements IBinaryRelation {

	private static final boolean THROW_EXCEPTION_IF_NOT_SOLVABLE = false;

	protected final RelationSymbol mRelationSymbol;
	protected final Rational mLhsCoefficient;
	protected final Monomial mLhsMonomial;
	protected final IPolynomialTerm mRhs;

	private ExplicitLhsPolynomialRelation(final RelationSymbol relationSymbol, final Rational lhsCoefficient,
			final Monomial lhsMonomial, final IPolynomialTerm rhs) {
		super();
		mRelationSymbol = relationSymbol;
		mLhsCoefficient = lhsCoefficient;
		mLhsMonomial = lhsMonomial;
		mRhs = rhs;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public Rational getLhsCoefficient() {
		return mLhsCoefficient;
	}

	public Monomial getLhsMonomial() {
		return mLhsMonomial;
	}

	public IPolynomialTerm getRhs() {
		return mRhs;
	}

	public static ExplicitLhsPolynomialRelation moveMonomialToLhs(final Script script, final Term subject,
			final PolynomialRelation polyRel) {

		final Monomial monomialOfSubject = polyRel.getPolynomialTerm().getExclusiveMonomialOfSubject(subject);
		if (monomialOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not exclusive variables");
			} else {
				return null;
			}
		}
		if (monomialOfSubject.getVariable2Exponent().get(subject) != Rational.ONE) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("roots not yet supported");
			} else {
				return null;
			}
		}
		final Rational coeffOfSubject;
		if (polyRel.getPolynomialTerm().isAffine()) {
			final Term singleVariable = monomialOfSubject.getSingleVariable();
			assert subject.equals(singleVariable);
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(singleVariable);
		} else {
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(monomialOfSubject);
		}
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}

		return new ExplicitLhsPolynomialRelation(polyRel.getRelationSymbol(), coeffOfSubject, monomialOfSubject,
				polyRel.getPolynomialTerm().removeAndNegate(monomialOfSubject));

	}

	public ExplicitLhsPolynomialRelation divInvertible(final Rational divisor) {
		if (divisor.equals(Rational.ZERO)) {
			throw new AssertionError("div by zero");
		}
		final IPolynomialTerm newRhs = mRhs.divInvertible(divisor);
		if (newRhs == null) {
			return null;
		}
		final Rational newLhsCoefficient = PolynomialTermUtils.divInvertible(mLhsMonomial.getSort(), mLhsCoefficient,
				divisor);
		if (newLhsCoefficient == null) {
			return null;
		}
		final RelationSymbol resultRelationSymbol = determineResultRelationSymbol(mLhsMonomial.getSort(),
				mRelationSymbol, divisor);
		return new ExplicitLhsPolynomialRelation(resultRelationSymbol, newLhsCoefficient, mLhsMonomial, newRhs);
	}

	private RelationSymbol determineResultRelationSymbol(final Sort sort, final RelationSymbol relationSymbol,
			final Rational divisor) {
		final RelationSymbol resultRelationSymbol = swapOfRelationSymbolRequired(divisor, sort)
				? relationSymbol.swapParameters()
				: relationSymbol;
		return resultRelationSymbol;
	}

	public static boolean swapOfRelationSymbolRequired(final Rational divisor, final Sort sort) {
		return divisor.isNegative() || (SmtSortUtils.isBitvecSort(sort) && SmtUtils.isBvMinusOne(divisor, sort));
	}

	public SolvedBinaryRelation divideByIntegerCoefficientForInequalities(final Script script,
			final Set<TermVariable> bannedForDivCapture) {
		if (mLhsCoefficient.equals(Rational.ZERO)) {
			throw new AssertionError("div by zero");
		}
		if (!SmtSortUtils.isIntSort(mLhsMonomial.getSort())) {
			throw new AssertionError("no int");
		}
		switch (mRelationSymbol) {
		case DISTINCT:
		case EQ:
			throw new AssertionError("no inequality");
		case GEQ:
		case GREATER:
		case LEQ:
		case LESS:
			break;
		default:
			throw new AssertionError("unknown value " + mRelationSymbol);
		}
		final Term rhsAsTerm = mRhs.toTerm(script);
		if (Arrays.stream(rhsAsTerm.getFreeVars()).anyMatch(bannedForDivCapture::contains)) {
			return null;
		}
		final Term rhs = SolveForSubjectUtils.constructRhsIntegerQuotient(script, mRelationSymbol, mRhs.toTerm(script),
				!mLhsCoefficient.isNegative(), mLhsCoefficient.toTerm(mLhsMonomial.getSort()));
		final RelationSymbol resultRelationSymbol = determineResultRelationSymbol(mLhsMonomial.getSort(),
				mRelationSymbol, mLhsCoefficient);
		return new SolvedBinaryRelation(mLhsMonomial.getSingleVariable(), rhs, resultRelationSymbol,
				Collections.emptyMap(), IntricateOperation.DIV_BY_INTEGER_CONSTANT);
	}

	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		throw new UnsupportedOperationException("not yet implemented");
	}

}
