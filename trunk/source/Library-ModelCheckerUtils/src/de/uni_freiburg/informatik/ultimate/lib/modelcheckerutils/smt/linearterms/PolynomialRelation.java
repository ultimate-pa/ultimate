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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.Case;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolutionBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.SupportingTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are
 * {@link PolynomialTerm}s or {@link AffineTerm}s and ▷ is a binary relation
 * symbol from the following list.
 * <p>
 * ▷ ∈ { =, !=, \<=, \<, \>=, \> }
 * </p>
 * <p>
 * Allows to return this relation as an SMT term in the following two forms:
 * <ul>
 * <li>positive normal form
 * <li>the form where a specific variable is on the left hand side and all other
 * summands are moved to the right hand side.
 * </ul>
 * </p>
 *
 * @author Leonard Fichtner
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolynomialRelation implements IBinaryRelation {

	protected static final String NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE = "No affine representation where desired variable is on left hand side";
	protected static final boolean TEMPORARY_POLYNOMIAL_TERM_TEST = false;
	private static final boolean THROW_EXCEPTION_IF_NOT_SOLVABLE = false;
	protected final Term mOriginalTerm;
	protected final RelationSymbol mRelationSymbol;
	protected final TrivialityStatus mTrivialityStatus;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the
	 * mOriginalTerm.
	 */
	protected final AbstractGeneralizedAffineTerm<Term> mPolynomialTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link PolynomialRelation} from {@link IPolynomialTerm} and
	 * {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
	 *
	 * @deprecated no constructor for this special case
	 */
	@Deprecated
	public PolynomialRelation(final Script script, final AbstractGeneralizedAffineTerm<?> term,
			final RelationSymbol relationSymbol) {
		mPolynomialTerm = Objects.requireNonNull(checkThenCast(term));
		mRelationSymbol = relationSymbol;

		mTrivialityStatus = computeTrivialityStatus(mPolynomialTerm, mRelationSymbol);
		if (VMUtils.areAssertionsEnabled()) {
			mOriginalTerm = script.term(mRelationSymbol.toString(), term.toTerm(script),
					SmtUtils.constructIntegerValue(script, term.getSort(), BigInteger.ZERO));
		} else {
			mOriginalTerm = null;
		}
	}

	public PolynomialRelation(final Script script, final TransformInequality transformInequality,
			final RelationSymbol relationSymbol, final AbstractGeneralizedAffineTerm<?> polyLhs,
			final AbstractGeneralizedAffineTerm<?> polyRhs, final Term originalTerm) {
		mOriginalTerm = originalTerm;
		final AbstractGeneralizedAffineTerm<Term> difference = sum(checkThenCast(polyLhs),
				mul(checkThenCast(polyRhs), Rational.MONE));
		final AbstractGeneralizedAffineTerm<Term> polyTerm;
		final RelationSymbol relationSymbolAfterTransformation;

		if (transformInequality != TransformInequality.NO_TRANFORMATION
				&& SmtSortUtils.isIntSort(difference.getSort())) {
			if (transformInequality == TransformInequality.STRICT2NONSTRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case GEQ:
				case LEQ:
					// relation symbol is not strict anyway
					polyTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case LESS:
					// increment polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.LEQ;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.GEQ;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else if (transformInequality == TransformInequality.NONSTRICT2STRICT) {
				switch (relationSymbol) {
				case DISTINCT:
				case EQ:
				case LESS:
				case GREATER:
					// relation symbol is strict anyway
					polyTerm = difference;
					relationSymbolAfterTransformation = relationSymbol;
					break;
				case GEQ:
					// increment polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.GREATER;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement polynomial term by one
					relationSymbolAfterTransformation = RelationSymbol.LESS;
					polyTerm = sum(difference, constructConstant(difference.getSort(), Rational.MONE));
					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else {
				throw new AssertionError("unknown case");
			}
		} else {
			polyTerm = difference;
			relationSymbolAfterTransformation = relationSymbol;
		}
		mPolynomialTerm = polyTerm;
		mRelationSymbol = relationSymbolAfterTransformation;
		mTrivialityStatus = computeTrivialityStatus(polyTerm, relationSymbolAfterTransformation);
	}

	private AbstractGeneralizedAffineTerm<Term> sum(final AbstractGeneralizedAffineTerm<Term> op1,
			final AbstractGeneralizedAffineTerm<Term> op2) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op1.isAffine() && op2.isAffine()) {
			result = AffineTerm.sum(op1, op2);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.sum(op1, op2);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	private AbstractGeneralizedAffineTerm<Term> mul(final AbstractGeneralizedAffineTerm<Term> op, final Rational r) {
		final AbstractGeneralizedAffineTerm<Term> result;
		if (op.isAffine()) {
			result = AffineTerm.mul(op, r);
		} else {
			final AbstractGeneralizedAffineTerm<?> polynomialSum = PolynomialTerm.mul(op, r);
			result = unsafeCast(polynomialSum);
		}
		return result;
	}

	private AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	/**
	 * Given a AbstractGeneralizedAffineTerm, check whether it is of Type AffineTerm
	 * and PolynomialTerm. If yes, cast it (UNSAFE) and return the result, throw an
	 * exception otherwise.
	 */
	private static AbstractGeneralizedAffineTerm<Term> checkThenCast(final AbstractGeneralizedAffineTerm<?> poly) {
		if (!(poly instanceof AffineTerm || poly instanceof PolynomialTerm)) {
			throw new IllegalArgumentException(
					"PolynomialRelation accepts only AffineTerm " + "and PolynomialTerm as internal terms.");
		}
		return unsafeCast(poly);
	}

	@SuppressWarnings("unchecked")
	private static AbstractGeneralizedAffineTerm<Term> unsafeCast(final AbstractGeneralizedAffineTerm<?> poly) {
		return (AbstractGeneralizedAffineTerm<Term>) poly;
	}

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<Term> term,
			final RelationSymbol symbol) {
		if (!term.isConstant()) {
			return TrivialityStatus.NONTRIVIAL;
		}

		switch (symbol) {
		case DISTINCT:
			return computeTrivialityStatus(term, a -> a != 0);
		case EQ:
			return computeTrivialityStatus(term, a -> a == 0);
		case LESS:
			return computeTrivialityStatus(term, a -> a < 0);
		case GREATER:
			return computeTrivialityStatus(term, a -> a > 0);
		case GEQ:
			return computeTrivialityStatus(term, a -> a >= 0);
		case LEQ:
			return computeTrivialityStatus(term, a -> a <= 0);
		default:
			throw new UnsupportedOperationException("unknown relation symbol: " + symbol);
		}
	}

	private static TrivialityStatus computeTrivialityStatus(final AbstractGeneralizedAffineTerm<Term> term,
			final Predicate<Integer> pred) {
		if (pred.test(term.getConstant().signum())) {
			return TrivialityStatus.EQUIVALENT_TO_TRUE;
		} else {
			return TrivialityStatus.EQUIVALENT_TO_FALSE;
		}
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public AbstractGeneralizedAffineTerm<Term> getPolynomialTerm() {
		return mPolynomialTerm;
	}

	/**
	 * Returns a term representation of this PolynomialRelation where each summand
	 * occurs only positive and the greater-than relation symbols are replaced by
	 * less-than relation symbols. If the term is equivalent to <i>true</i> (resp.
	 * <i>false</i>) we return <i>true</i> (resp. <i>false</i>).
	 */
	public Term positiveNormalForm(final Script script) {
		if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_TRUE) {
			return script.term("true");
		} else if (mTrivialityStatus == TrivialityStatus.EQUIVALENT_TO_FALSE) {
			return script.term("false");
		} else {
			assert mTrivialityStatus == TrivialityStatus.NONTRIVIAL;
			final List<Term> lhsSummands = new ArrayList<>();
			final List<Term> rhsSummands = new ArrayList<>();
			for (final Entry<Term, Rational> entry : mPolynomialTerm.getAbstractVariable2Coefficient().entrySet()) {
				final Term abstractVariableAsTerm = mPolynomialTerm.abstractVariableToTerm(script, entry.getKey());
				if (entry.getValue().isNegative()) {
					rhsSummands.add(product(script, entry.getValue().abs(), abstractVariableAsTerm));
				} else {
					lhsSummands.add(product(script, entry.getValue(), abstractVariableAsTerm));
				}
			}
			if (mPolynomialTerm.getConstant() != Rational.ZERO) {
				if (mPolynomialTerm.getConstant().isNegative()) {
					rhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant().abs(),
							mPolynomialTerm.getSort()));
				} else {
					lhsSummands.add(
							SmtUtils.rational2Term(script, mPolynomialTerm.getConstant(), mPolynomialTerm.getSort()));
				}
			}
			final Term lhsTerm = SmtUtils.sum(script, mPolynomialTerm.getSort(),
					lhsSummands.toArray(new Term[lhsSummands.size()]));
			final Term rhsTerm = SmtUtils.sum(script, mPolynomialTerm.getSort(),
					rhsSummands.toArray(new Term[rhsSummands.size()]));
			final Term result = BinaryRelation.constructLessNormalForm(script, mRelationSymbol, lhsTerm, rhsTerm);
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					result) != LBool.SAT : "transformation to positive normal form " + "unsound";
			return result;
		}
	}

	private static LBool isEquivalent(final Script script, final Term term1, final Term term2) {
		Term comp = script.term("=", term1, term2);
		comp = script.term("not", comp);
		final LBool sat = Util.checkSat(script, comp);
		return sat;
	}

	private static LBool assumptionImpliesEquivalence(final Script script, final Term originalTerm,
			final Term relationToTerm, final Map<AssumptionForSolvability, Term> additionalAssumptions) {
		final Term konJ = SmtUtils.and(script, additionalAssumptions.values());
		final Term impli1 = SmtUtils.implies(script, konJ, relationToTerm);
		final Term impli2 = SmtUtils.implies(script, konJ, originalTerm);
		return isEquivalent(script, impli1, impli2);
	}

	private static Term product(final Script script, final Rational rational, final Term term) {
		if (rational.equals(Rational.ONE)) {
			return term;
		} else if (rational.equals(Rational.MONE)) {
			return SmtUtils.neg(script, term);
		} else {
			final Term coefficient = SmtUtils.rational2Term(script, rational, term.getSort());
			return SmtUtils.mul(script, term.getSort(), coefficient, term);
		}
	}

	/**
	 * Returns a {@link SolvedBinaryRelation} that is equivalent to this
	 * PolynomialRelation or null if we cannot find such a
	 * {@link SolvedBinaryRelation}.
	 */
	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		if (!isVariable(subject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not a variable");
			} else {
				return null;
			}
		}
		final Term abstractVarOfSubject = getTheAbstractVarOfSubject(subject);
		if (abstractVarOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject occurs in several abstract variables");
			} else {
				return null;
			}
		}
		if (divisionByVariablesNecessary(abstractVarOfSubject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("Division by variables needs case distinction");
			} else {
				return null;
			}
		}
		final Rational coeffOfSubject = mPolynomialTerm.getAbstractVariable2Coefficient().get(abstractVarOfSubject);
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}
		if (isBvAndCantBeSolved(coeffOfSubject, abstractVarOfSubject)) {
			// for bitvectors we may only divide by 1 or -1
			// reason: consider bitvectors of length 8 (i.e., 256=0)
			// then e.g., 2*x = 0 is not equivalent to x = 0 because
			// for x=128 the first equation hold but the second does not
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException(
						"for bitvector subjects only coefficients 1 and -1 are supported");
			} else {
				return null;
			}
		}

		final Term simpliySolvableRhsTerm = constructRhsForAbstractVariable(script, abstractVarOfSubject,
				coeffOfSubject);
		final AssumptionMapBuilder assumptionMapBuilder = new AssumptionMapBuilder(script);
		Term rhsTerm;
		if (simpliySolvableRhsTerm == null) {
			final Term rhsTermWithoutDivision = constructRhsForAbstractVariable(script, abstractVarOfSubject,
					Rational.ONE);
			rhsTerm = constructRhsIntegerQuotient(script, mRelationSymbol, rhsTermWithoutDivision,
					!coeffOfSubject.isNegative(), coeffOfSubject.toTerm(rhsTermWithoutDivision.getSort()));
			// EQ and DISTINCT need Modulo Assumption
			if (isEqOrDistinct(mRelationSymbol)) {
				assumptionMapBuilder.putDivisibleByConstant(rhsTermWithoutDivision,
						coeffOfSubject.toTerm(mPolynomialTerm.getSort()));
			}
			// cases LEQ, LESS, GREATER, GEQ do nothing

		} else {
			rhsTerm = simpliySolvableRhsTerm;
		}

		final RelationSymbol resultRelationSymbol;
		if (isNegative(coeffOfSubject)) {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = BinaryRelation.swapParameters(mRelationSymbol);
		} else {
			resultRelationSymbol = mRelationSymbol;
		}

		final SolvedBinaryRelation result = new SolvedBinaryRelation(subject, rhsTerm, resultRelationSymbol,
				assumptionMapBuilder.getExplicitAssumptionMap());
		final Term relationToTerm = result.asTerm(script);
		if (!assumptionMapBuilder.isEmpty()) {
			assert script instanceof INonSolverScript
					|| assumptionImpliesEquivalence(script, mOriginalTerm, relationToTerm, assumptionMapBuilder
							.getExplicitAssumptionMap()) != LBool.SAT : "transformation to AffineRelation unsound";
		} else {
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					relationToTerm) != LBool.SAT : "transformation to AffineRelation unsound";
		}
		return result;
	}

	/**
	 * Returns a {@link MultiCaseSolvedBinaryRelation} that is equivalent to this
	 * PolynomialRelation or null if we cannot find such a
	 * {@link MultiCaseSolvedBinaryRelation}.
	 */
	public MultiCaseSolvedBinaryRelation solveForSubject(final Script script, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf) {
		boolean subjectIsNotAVariableButOccursInDivOrModSubterm = false;
		ApplicationTerm allowedSubterm = null;
		if (!isVariable(subject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not a variable");
			} else {
				allowedSubterm = searchModOrDivSubterm(mPolynomialTerm.toTerm(script), script, subject);
				if (allowedSubterm != null) {
					subjectIsNotAVariableButOccursInDivOrModSubterm = true;
				} else {
					return null;
				}
			}
		}
		Term abstractVarOfSubject = getTheAbstractVarOfSubject(subject);
		if (subjectIsNotAVariableButOccursInDivOrModSubterm && (abstractVarOfSubject == null)) {
			abstractVarOfSubject = subject;
		}
		if (abstractVarOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject occurs in several abstract variables");
			} else {
				return null;
			}
		}
		Rational coeffOfSubject = mPolynomialTerm.getAbstractVariable2Coefficient().get(abstractVarOfSubject);
		if (subjectIsNotAVariableButOccursInDivOrModSubterm && (coeffOfSubject == null)) {
			if (!(allowedSubterm.getParameters()[1] instanceof ConstantTerm)) {
				// divisor of div/mod is not a constant
				return null;
			}
			final ConstantTerm coeffTerm = (ConstantTerm) allowedSubterm.getParameters()[1];
			coeffOfSubject = SmtUtils.convertConstantTermToRational(coeffTerm);
		}
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}
		if (isBvAndCantBeSolved(coeffOfSubject, abstractVarOfSubject)) {
			// for bitvectors we may only divide by 1 or -1
			// reason: consider bitvectors of length 8 (i.e., 256=0)
			// then e.g., 2*x = 0 is not equivalent to x = 0 because
			// for x=128 the first equation hold but the second does not
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException(
						"for bitvector subjects only coefficients 1 and -1 are supported");
			} else {
				return null;
			}
		}



		final Term stageTwoRhs;
		final Rational stageTwoCoefficient;
		final boolean isOriginalCoefficientPositive = !isNegative(coeffOfSubject);
		{
			final Term simplySolvableRhsTerm = constructRhsForAbstractVariable(script, abstractVarOfSubject,
					coeffOfSubject);
			if (simplySolvableRhsTerm == null) {
				stageTwoRhs = constructRhsForAbstractVariable(script, abstractVarOfSubject, Rational.ONE);
				stageTwoCoefficient = coeffOfSubject;
			} else {
				stageTwoRhs = simplySolvableRhsTerm;
				stageTwoCoefficient = null;
			}
		}

		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		if (subjectIsNotAVariableButOccursInDivOrModSubterm) {
				// Solve for subject in affineterm with a parameter of form (mod/div (subterm
				// with subject) constant)
				final Sort termSort = mPolynomialTerm.getSort();
				// recVarName ensures different names in each recursion, since AffineRelation is
				// made new each time
				final int recVarName = allowedSubterm.toString().length();
				final TermVariable auxDiv = script.variable("aux_div_" + recVarName, termSort);
				final TermVariable auxMod = script.variable("aux_mod_" + recVarName, termSort);

				final Term multiplication = SmtUtils.mul(script, termSort,
						SmtUtils.rational2Term(script, coeffOfSubject, termSort), auxDiv);
				final Term sum = SmtUtils.sum(script, termSort, auxMod, multiplication);

				final AbstractGeneralizedAffineTerm recursion = (AbstractGeneralizedAffineTerm) new AffineTermTransformer(
						script).transform(allowedSubterm.getParameters()[0]);
				if (!recursion.isVariable(subject)) {
					// recursiv call for terms of form: "(mod ...(mod subject const1)... const 2)"
					final MultiCaseSolvedBinaryRelation mcsbr = PolynomialRelation
							.convert(script, SmtUtils.binaryEquality(script, allowedSubterm.getParameters()[0], sum))
							.solveForSubject(script, subject, xnf);
					final SupportingTerm recSupTerm = new SupportingTerm(mcsbr.asTerm(script),
							IntricateOperation.MUL_BY_INTEGER_CONSTANT, mcsbr.getAuxiliaryVariables());
					mcsb.conjoinWithConjunction(recSupTerm);
				} else {
					// solve terms of form (mod (subterm) const) where subterm contains x but is no
					// mod or div term
					final SolvedBinaryRelation sbr = PolynomialRelation
							.convert(script, SmtUtils.binaryEquality(script, allowedSubterm.getParameters()[0], sum))
							.solveForSubject(script, subject);
					mcsb.conjoinWithConjunction(sbr);
				}

				// construct SupportingTerm (t = aux_mod) or (t = aux_div)
				final Set<TermVariable> setAuxVars = new HashSet<>();
				// substitute allowedSubterm with corresponding aux variable for terms of form
				// (+ (mod/div subject const) const)
				final Map<Term, Term> submap = new HashMap<>();
				if (allowedSubterm.getFunction().getName().contentEquals("mod")) {
					submap.put(allowedSubterm, auxMod);
					setAuxVars.add(auxMod);
					mcsb.reportAdditionalAuxiliaryVariable(auxDiv);
				} else if (allowedSubterm.getFunction().getName().contentEquals("div")) {
					setAuxVars.add(auxDiv);
					submap.put(allowedSubterm, auxDiv);
				}
				final Substitution sub = new Substitution(script, submap);
				final Term auxModEqualsTerm = sub.transform(mOriginalTerm);
				final SupportingTerm auxEquals = new SupportingTerm(auxModEqualsTerm,
						IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);
				setAuxVars.add(auxMod);

				// construct SupportingTerm (0<=aux_mod)
				final Term auxModGreaterZeroTerm = SmtUtils.geq(script, auxMod, Rational.ZERO.toTerm(termSort));
				final SupportingTerm auxModGreaterZero = new SupportingTerm(auxModGreaterZeroTerm,
						IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

				// construct SupportingTerm (aux_mod < k)
				final Term auxModLessCoefTerm = SmtUtils.less(script, auxMod, coeffOfSubject.toTerm(termSort));
				final SupportingTerm auxModLessCoef = new SupportingTerm(auxModLessCoefTerm,
						IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

				mcsb.conjoinWithConjunction(auxModLessCoef, auxEquals, auxModGreaterZero);
				final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
					assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
							result.asTerm(script)) != LBool.SAT : "solveForSubject unsound";
				return result;
			}
		final Collection<Case> cases = new ArrayList<>();
		final Term[] divisorAsArray;
		if (divisionByVariablesNecessary(abstractVarOfSubject)) {
			// TODO 13.11.2019 Leonard: When we divide by variables we could actually
			// sometimes simplify the resulting division, in the case that this variable is
			// not zero (and therefore we can simplify f.ex. x/x to 1). Also we could
			// sometimes get conjuncts like x!=0, that are already in the case distinction.
			// Handle this in the MultiCaseSolutionBuilder?
			// At the moment this seems like much work relative to little effect, so I was
			// asked to leave this comment here for the future.
			final List<Term> twoCaseVariables = new ArrayList<>();
			final Set<SupportingTerm> distinctZeroSupportingTerms = new HashSet<>();
			final List<Term> threeCaseVariables = new ArrayList<>();
			final List<SupportingTerm> isNegativeSupportingTerms = new ArrayList<>();
			final List<SupportingTerm> isPositiveSupportingTerms = new ArrayList<>();
			final List<Term> divisorAsList = new ArrayList<>();
			if (stageTwoCoefficient != null) {
				divisorAsList.add(stageTwoCoefficient.toTerm(mPolynomialTerm.getSort()));
			}
			for (final Entry<Term, Rational> var2exp : ((Monomial) abstractVarOfSubject).getVariable2Exponent()
					.entrySet()) {
				assert var2exp.getValue().isIntegral();
				if (var2exp.getKey() == subject) {
					// do nothing
				} else {
					cases.add(constructDivByVarEqualZeroCase(script, var2exp.getKey(), stageTwoRhs, mRelationSymbol, xnf));
					final int exp = var2exp.getValue().numerator().intValueExact();
					for (int i=0; i<exp; i++) {
						divisorAsList.add(var2exp.getKey());
					}
					if (isEqOrDistinct(mRelationSymbol) || exp % 2 == 0) {
						twoCaseVariables.add(var2exp.getKey());
						distinctZeroSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(), negateForCnf(RelationSymbol.DISTINCT, xnf)));
					} else {
						// We have to distinguish the case now into two cases,
						// since the RelationSymbol has to be swapped, when we divide by a negative
						// variable.
						threeCaseVariables.add(var2exp.getKey());
						isNegativeSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(), negateForCnf(RelationSymbol.LESS, xnf)));
						isPositiveSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(), negateForCnf(RelationSymbol.GREATER, xnf)));
					}
				}
			}
			divisorAsArray = divisorAsList.toArray(new Term[divisorAsList.size()]);
//			final Term resultRhs = SmtUtils.division(script, rhsTerm.getSort(), divisorAsList.toArray(new Term[divisorAsList.size()]));
			if (threeCaseVariables.isEmpty()) {
				final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs, isOriginalCoefficientPositive, divisorAsArray);
				final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
				if (isDerIntegerDivisionSupportingTermRequired(xnf)) {
					final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
							stageTwoRhs, divisorAsArray);
					thisCaseSupportingTerms.add(divisibilityConstraint);
				}
				cases.add(new Case(sbr, thisCaseSupportingTerms, xnf));
			} else {
				if (threeCaseVariables.size() > 30) {
					throw new UnsupportedOperationException("Exponential blowup too huge. Exponent is " + threeCaseVariables.size());
				}
				final int numberOfCases = BigInteger.valueOf(2).pow(threeCaseVariables.size()).intValueExact();
				for (int i = 0; i < numberOfCases; i++) {
					// if bit is set this means that we assume that variable is negative
					final boolean isDivisorPositive = ((BigInteger.valueOf(i).bitCount() % 2 == 0) == isOriginalCoefficientPositive);
					final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs, isDivisorPositive, divisorAsArray);
					final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
					for (int j = 0; j< threeCaseVariables.size(); j++) {
						SupportingTerm posOrNegSupportingTerm;
						if (BigInteger.valueOf(i).testBit(j)) {
							posOrNegSupportingTerm = isNegativeSupportingTerms.get(j);
						} else {
							posOrNegSupportingTerm = isPositiveSupportingTerms.get(j);
						}
						thisCaseSupportingTerms.add(posOrNegSupportingTerm);
					}
					if (isDerIntegerDivisionSupportingTermRequired(xnf)) {
						final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
								stageTwoRhs, divisorAsArray);
						thisCaseSupportingTerms.add(divisibilityConstraint);
					}
					cases.add(new Case(sbr, thisCaseSupportingTerms, xnf));
				}
			}
		} else {
			final boolean isDivisorPositive = isOriginalCoefficientPositive;
			if (stageTwoCoefficient == null) {
				divisorAsArray = new Term[0];
			} else {
				divisorAsArray = new Term[] { stageTwoCoefficient.toTerm(mPolynomialTerm.getSort()) };
			}
			final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs,
					isDivisorPositive, divisorAsArray);
			final Set<SupportingTerm> supportingTerms;
			if (stageTwoCoefficient != null && isDerIntegerDivisionSupportingTermRequired(xnf)) {
				final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
						stageTwoRhs, divisorAsArray);
				supportingTerms = Collections.singleton(divisibilityConstraint);
			} else {
				supportingTerms = Collections.emptySet();
			}
			cases.add(new Case(sbr, supportingTerms , xnf));
		}
		if (isAntiDerIntegerDivisionCaseRequired(xnf)) {
			final Case result = constructAntiDerIntegerDivisibilityCase(script, xnf, stageTwoRhs,
					divisorAsArray);
			cases.add(result);
		}
		mcsb.conjoinWithDnf(cases);

		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		if (!subjectIsNotAVariableButOccursInDivOrModSubterm) {
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					result.asTerm(script)) != LBool.SAT : "solveForSubject unsound";
		}
		return result;
	}

	private RelationSymbol negateForCnf(final RelationSymbol symb, final Xnf xnf) {
		if (xnf == Xnf.CNF) {
			return BinaryRelation.negateRelation(symb);
		} else {
			return symb;
		}
	}

	private boolean isDerIntegerDivisionSupportingTermRequired(final Xnf xnf) {
		return SmtSortUtils.isIntSort(mPolynomialTerm.getSort()) &&
				((mRelationSymbol == RelationSymbol.EQ) && xnf == Xnf.DNF
				|| (mRelationSymbol == RelationSymbol.DISTINCT) && xnf == Xnf.CNF);
	}

	private SupportingTerm constructDerIntegerDivisionSupportingTerm(final Script script, final Term stageTwoRhs,
			final Term[] divisorAsArray) {
		final boolean negate = mRelationSymbol.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script,
				negate, stageTwoRhs, SmtUtils.mul(script, mPolynomialTerm.getSort(), divisorAsArray));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
		return divisibilityConstraint;
	}

	private boolean isAntiDerIntegerDivisionCaseRequired(final Xnf xnf) {
		return SmtSortUtils.isIntSort(mPolynomialTerm.getSort()) &&
				((mRelationSymbol == RelationSymbol.DISTINCT) && xnf == Xnf.DNF
				|| (mRelationSymbol == RelationSymbol.EQ) && xnf == Xnf.CNF);
	}

	private Case constructAntiDerIntegerDivisibilityCase(final Script script,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Term stageTwoRhs, final Term[] divisorAsArray) {
		final Set<SupportingTerm> suppTerms = new HashSet<>();
		final boolean negate = mRelationSymbol.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script, negate, stageTwoRhs,
				SmtUtils.mul(script, mPolynomialTerm.getSort(), divisorAsArray));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
		suppTerms.add(divisibilityConstraint);
		final SupportingTerm inRelationToZero = constructInRelationToZeroSupportingTerm(script,
				SmtUtils.mul(script, mPolynomialTerm.getSort(), divisorAsArray),
				negateForCnf(RelationSymbol.DISTINCT, xnf));
		suppTerms.add(inRelationToZero);
		final Case result = new Case(null, suppTerms, xnf);
		return result;
	}

	private SolvedBinaryRelation constructSolvedBinaryRelation(final Script script, final Term subject,
			final Term stageTwoRhs, final boolean isDivisorPositive, final Term[] divisor) {
		final Term resultRhs;
		if (divisor.length == 0) {
			resultRhs = stageTwoRhs;
		} else {
			if (SmtSortUtils.isIntSort(stageTwoRhs.getSort())) {
				resultRhs = constructRhsIntegerQuotient(script, mRelationSymbol, stageTwoRhs, isDivisorPositive, divisor);
			} else {
				resultRhs = SmtUtils.divReal(script, prepend(stageTwoRhs, divisor));
			}
		}
		final RelationSymbol resultRelationSymbol;
		if (isDivisorPositive) {
			resultRelationSymbol = mRelationSymbol;
		} else {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = BinaryRelation.swapParameters(mRelationSymbol);
		}
		final SolvedBinaryRelation sbr = new SolvedBinaryRelation(subject, resultRhs, resultRelationSymbol, Collections.emptyMap());
		return sbr;
	}


	/**
	 * go thru the parameters of the affineTerm and search for a term of form (mod
	 * subterm const) or (div subterm const) where subterm contains the subject
	 *
	 * @return (mod/div ... (mod/div subject const)... const)
	 */
	private ApplicationTerm searchModOrDivSubterm(final Term affineTerm, final Script script, final Term subject) {
		if (affineTerm instanceof ApplicationTerm) {
			final ApplicationTerm appAffineTerm = (ApplicationTerm) affineTerm;
			for (final Term para : appAffineTerm.getParameters()) {
				final boolean containsSubject = new ContainsSubterm(subject).containsSubterm(para);
				if (containsSubject && para instanceof ApplicationTerm) {
					ApplicationTerm paraAppTerm = ((ApplicationTerm) para);
					if (paraAppTerm.getFunction().getName().contentEquals("div")) {
						return paraAppTerm;
					} else if (paraAppTerm.getFunction().getName().contentEquals("mod")) {
						// optimization: simplifies (mod (mod...(mod x k)...k) k) to (mod x k)
						while (!paraAppTerm.getParameters()[0].equals(subject)) {
							final ApplicationTerm subterm = ((ApplicationTerm) paraAppTerm.getParameters()[0]);
							if (subterm.getFunction().getName().contentEquals("mod")) {
								if (subterm.getParameters()[1].equals(paraAppTerm.getParameters()[1])) {
									paraAppTerm = subterm;
								} else {
									return paraAppTerm;
								}
							} else {
								return paraAppTerm;
							}
						}
						return paraAppTerm;
					} else {
						return searchModOrDivSubterm(para, script, subject);
					}
				}
			}
		}
		return null;
	}

	private static Term constructDivisibilityConstraint(final Script script, final boolean negate, final Term divident,
			final Term divisor) {
		final Term modTerm = SmtUtils.mod(script, divident, divisor);
		final Term tmp = SmtUtils.binaryEquality(script, modTerm,
				SmtUtils.constructIntegerValue(script, SmtSortUtils.getIntSort(script), BigInteger.ZERO));
		final Term result;
		if (negate) {
			result = SmtUtils.not(script, tmp);
		} else {
			result = tmp;
		}
		return result;
	}

	@Deprecated
	private Case constructDivByVarEqualZeroCase(final Script script, final IntermediateCase previousCase,
			final Term var) {
		final RelationSymbol relSym = previousCase.getIntermediateRelationSymbol();
		final Term rhs = previousCase.getIntermediateRhs();
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>(previousCase.getSupportingTerms());
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());
		final Term varEqualZero = SmtUtils.binaryEquality(script, zeroTerm, var);
		suppTerms.add(new SupportingTerm(varEqualZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		final Term rhsRelationZeroTerm;
		switch (relSym) {
		case EQ:
			rhsRelationZeroTerm = SmtUtils.binaryEquality(script, zeroTerm, rhs);
			break;
		case DISTINCT:
			rhsRelationZeroTerm = SmtUtils.distinct(script, zeroTerm, rhs);
			break;
		case LEQ:
			rhsRelationZeroTerm = SmtUtils.leq(script, zeroTerm, rhs);
			break;
		case LESS:
			rhsRelationZeroTerm = SmtUtils.less(script, zeroTerm, rhs);
			break;
		case GEQ:
			rhsRelationZeroTerm = SmtUtils.geq(script, zeroTerm, rhs);
			break;
		case GREATER:
			rhsRelationZeroTerm = SmtUtils.greater(script, zeroTerm, rhs);
			break;
		default:
			throw new AssertionError("Unknown RelationSymbol: " + relSym);
		}
		suppTerms.add(
				new SupportingTerm(rhsRelationZeroTerm, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new Case(null, suppTerms, MultiCaseSolvedBinaryRelation.Xnf.DNF);
	}


	private Case constructDivByVarEqualZeroCase(final Script script, final Term divisorVar, final Term rhs,
			final RelationSymbol relSym, final Xnf xnf) {
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>();
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());
		final Term varEqualZero = SmtUtils.binaryEquality(script, zeroTerm, divisorVar);
		final SupportingTerm st;
		switch (xnf) {
		case CNF:
			st = new SupportingTerm(SmtUtils.not(script, varEqualZero), IntricateOperation.DIV_BY_NONCONSTANT,
					Collections.emptySet());
			break;
		case DNF:
			st = new SupportingTerm(varEqualZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
			break;
		default:
			throw new AssertionError("unknown value " + xnf);
		}
		suppTerms.add(st);
		final Term rhsRelationZeroTerm;
		switch (relSym) {
		case EQ:
			rhsRelationZeroTerm = SmtUtils.binaryEquality(script, zeroTerm, rhs);
			break;
		case DISTINCT:
			rhsRelationZeroTerm = SmtUtils.distinct(script, zeroTerm, rhs);
			break;
		case LEQ:
			rhsRelationZeroTerm = SmtUtils.leq(script, zeroTerm, rhs);
			break;
		case LESS:
			rhsRelationZeroTerm = SmtUtils.less(script, zeroTerm, rhs);
			break;
		case GEQ:
			rhsRelationZeroTerm = SmtUtils.geq(script, zeroTerm, rhs);
			break;
		case GREATER:
			rhsRelationZeroTerm = SmtUtils.greater(script, zeroTerm, rhs);
			break;
		default:
			throw new AssertionError("Unknown RelationSymbol: " + relSym);
		}
		suppTerms.add(
				new SupportingTerm(rhsRelationZeroTerm, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new Case(null, suppTerms, xnf);
	}

	private IntermediateCase constructDivByVarDistinctZeroCase(final Script script, final IntermediateCase previousCase,
			final Entry<Term, Rational> var2exp) {
		final RelationSymbol relSym = previousCase.getIntermediateRelationSymbol();
		final Term rhs = previousCase.getIntermediateRhs();
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>(previousCase.getSupportingTerms());
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());

		assert var2exp.getValue().isIntegral();
		final int exp = var2exp.getValue().numerator().intValueExact();
		final Term rhsDividedByVar = divideTermByPower(script, rhs, var2exp.getKey(), exp);

		final Term varDistinctZero = SmtUtils.distinct(script, zeroTerm, var2exp.getKey());
		suppTerms.add(
				new SupportingTerm(varDistinctZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));

		if (SmtSortUtils.isIntSort(mPolynomialTerm.getSort()) && isEqOrDistinct(relSym)) {
			final Term[] vars = new Term[exp];
			for (int i = 0; i < vars.length; i++) {
				vars[i] = var2exp.getKey();
			}
			final Term varPowExp = SmtUtils.mul(script, mPolynomialTerm.getSort(), vars);
			final Term rhsModVarPowExp = SmtUtils.mod(script, rhs, varPowExp);
			final Term rhsDivisibleByVarPowExp = SmtUtils.binaryEquality(script, zeroTerm, rhsModVarPowExp);
			suppTerms.add(new SupportingTerm(rhsDivisibleByVarPowExp, IntricateOperation.DIV_BY_NONCONSTANT,
					Collections.emptySet()));
		}

		return new IntermediateCase(suppTerms, MultiCaseSolvedBinaryRelation.Xnf.DNF, rhsDividedByVar, relSym);
	}

	private IntermediateCase constructDivByVarGreaterZeroCase(final Script script, final IntermediateCase previousCase,
			final Entry<Term, Rational> var2exp) {
		final RelationSymbol relSym = previousCase.getIntermediateRelationSymbol();
		final Term rhs = previousCase.getIntermediateRhs();
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>(previousCase.getSupportingTerms());
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());

		assert var2exp.getValue().isIntegral();
		final int exp = var2exp.getValue().numerator().intValueExact();
		final Term rhsDividedByVar = divideTermByPower(script, rhs, var2exp.getKey(), exp);

		final Term varGreaterZero = SmtUtils.greater(script, var2exp.getKey(), zeroTerm);
		suppTerms
				.add(new SupportingTerm(varGreaterZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new IntermediateCase(suppTerms, MultiCaseSolvedBinaryRelation.Xnf.DNF, rhsDividedByVar, relSym);
	}

	private IntermediateCase constructDivByVarLessZeroCase(final Script script, final IntermediateCase previousCase,
			final Entry<Term, Rational> var2exp) {
		assert var2exp.getValue().isIntegral();
		final int exp = var2exp.getValue().numerator().intValueExact();
		assert exp % 2 == 1 : "If the exponent is even you don't need to distinguish less and greater, "
				+ "therefore use constructDivByVarDistinctZeroCase to avoid unnecessary big MCSBs";
		final RelationSymbol relSym = BinaryRelation.swapParameters(previousCase.getIntermediateRelationSymbol());
		final Term rhs = previousCase.getIntermediateRhs();
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>(previousCase.getSupportingTerms());
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());

		final Term rhsDividedByVar = divideTermByPower(script, rhs, var2exp.getKey(), exp);

		final Term varLessZero = SmtUtils.less(script, var2exp.getKey(), zeroTerm);
		suppTerms.add(new SupportingTerm(varLessZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new IntermediateCase(suppTerms, MultiCaseSolvedBinaryRelation.Xnf.DNF, rhsDividedByVar, relSym);
	}

	private SupportingTerm constructInRelationToZeroSupportingTerm(final Script script, final Term term, final RelationSymbol relSym) {
		final Term zero = SmtUtils.rational2Term(script, Rational.ZERO, term.getSort());
		final Term termRelZero = script.term(relSym.toString(), term, zero);
		return new SupportingTerm(termRelZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
	}

	private Term divideTermByPower(final Script script, final Term dividend, final Term divisor, final int exponent) {
		final Term[] division = new Term[exponent + 1];
		division[0] = dividend;
		if (exponent >= 2) {
			for (int i = 1; i < exponent + 1; i++) {
				division[i] = divisor;
			}
		} else {
			division[1] = divisor;
		}
		if (SmtSortUtils.isRealSort(mPolynomialTerm.getSort())) {
			return SmtUtils.divReal(script, division);
		} else if (SmtSortUtils.isIntSort(mPolynomialTerm.getSort())) {
			return SmtUtils.divInt(script, division);
		} else {
			throw new UnsupportedOperationException("PolynomialRelations of this sort are not supported.");
		}
	}

	private ArrayList<?> transformCaseIntoCollection(final Case c) {
		final ArrayList<Object> collection = new ArrayList<>();
		for (final SupportingTerm supp : c.getSupportingTerms()) {
			collection.add(supp);
		}
		if (c.getSolvedBinaryRelation() == null) {
			return collection;
		}
		collection.add(c.getSolvedBinaryRelation());
		return collection;
	}

	/**
	 * @return true iff the relation ψ ▷ φ has (after simplification) a form where ψ
	 *         and φ are both affine terms.
	 */
	public boolean isAffine() {
		return mPolynomialTerm.isAffine();
	}

	/**
	 * Try to bring everything but abstractVarOfSubject to the right-hand side. Try
	 * to divide the coefficient of every other variable and the constant by the
	 * coeffOfAbstractVar. If the sort is not real and for some coefficient the
	 * quotient is not integral return null. Otherwise return the {@link Term}
	 * representation of the right-hand side.
	 */
	private Term constructRhsForAbstractVariable(final Script script, final Term abstractVarOfSubject,
			final Rational coeffOfAbstractVar) {
		final List<Term> rhsSummands = new ArrayList<>(mPolynomialTerm.getAbstractVariable2Coefficient().size());
		for (final Entry<Term, Rational> entry : mPolynomialTerm.getAbstractVariable2Coefficient().entrySet()) {
			if (abstractVarOfSubject == entry.getKey()) {
				// do nothing
			} else {
				final Rational newCoeff;
				if (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())) {
					// This only works because we know that in our cases coeffOfAbstractVar is
					// always
					// its own multiplicative inverse.
					newCoeff = entry.getValue().mul(coeffOfAbstractVar);
				} else {
					newCoeff = entry.getValue().div(coeffOfAbstractVar);
				}
				if (newCoeff.isIntegral() || SmtSortUtils.isRealSort(mPolynomialTerm.getSort())) {
					if (entry.getKey() instanceof Monomial) {
						rhsSummands.add(product(script, newCoeff.negate(), ((Monomial) entry.getKey()).toTerm(script)));
					} else {
						rhsSummands.add(product(script, newCoeff.negate(), entry.getKey()));
					}
				} else {
					if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
						throw new UnsupportedOperationException(
								"some coefficient not divisible by coefficient of subject");
					} else {
						return null;
					}
				}
			}
		}
		if (!mPolynomialTerm.getConstant().equals(Rational.ZERO)) {
			final Rational newConstant;
			if (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())) {
				// This only works because we know that in our cases coeffOfAbstractVar is
				// always
				// its own multiplicative inverse.
				newConstant = mPolynomialTerm.getConstant().mul(coeffOfAbstractVar);
			} else {
				newConstant = mPolynomialTerm.getConstant().div(coeffOfAbstractVar);
			}
			if (newConstant.isIntegral() || SmtSortUtils.isRealSort(mPolynomialTerm.getSort())) {
				rhsSummands.add(SmtUtils.rational2Term(script, newConstant.negate(), mPolynomialTerm.getSort()));
			} else {
				if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
					throw new UnsupportedOperationException("some constant not divisible by coefficient of subject");
				} else {
					return null;
				}
			}
		}
		final Term rhsTerm = SmtUtils.sum(script, mPolynomialTerm.getSort(),
				rhsSummands.toArray(new Term[rhsSummands.size()]));
		return rhsTerm;
	}

	/**
	 * If we divide an integer RHS, the result is nontrivial. If we just apply
	 * division some information related to divisibility is lost.
	 * <ul>
	 * <li>If the relation symbol is EQ or DISTINCT, the lost information is that
	 * the RHS was (resp. was not) divisible by the divisor. And can be added later.
	 * </li>
	 * <li>Otherwise, the lost information is more complicated, we can not easily
	 * add it later. Instead, we construct a more complicated quotient that depends
	 * on
	 * <ul>
	 * <li>the sign of the divident's values</li>
	 * <li>the relation symbol</li>
	 * </ul>
	 * and ensures that no information is lost.</li>
	 * </ul>
	 */
	private static Term constructRhsIntegerQuotient(final Script script, final RelationSymbol relSymb,
			final Term rhs, final boolean divisorIsPositive, final Term... divisor) {
		final Term result;
		switch (relSymb) {
		case LESS:
			if (divisorIsPositive) {
				// k*x < t is equivalent to x < (t-1 div k)+1 for positive k
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.ONE, divisor);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.MONE, divisor);
			}
			break;
		case GREATER:
			// k*x > t is equivalent to x > (t div k) for all k
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case LEQ:
			// k*x <= t is equivalent to x <= (t div k) for positive k
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case GEQ:
			if (divisorIsPositive) {
				// k*x >= t is equivalent to x >= (t - 1 div k) + 1 for positive k
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.ONE, divisor);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				result = constructRhsIntegerQuotientHelper(script, rhs, Rational.MONE, divisor);
			}
			break;
		case EQ:
			// Default quotient, additional divisibility information has to be added later
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		case DISTINCT:
			// Default quotient, additional divisibility information has to be added later
			result = SmtUtils.division(script, rhs.getSort(), prepend(rhs, divisor));
			break;
		default:
			throw new AssertionError("unknown relation symbol: " + relSymb);
		}
		return result;
	}

	/**
	 * Construct quotient
	 *
	 * <pre>
	 * ((divident - 1) / divisor) + postDivisionOffset
	 * </pre>
	 *
	 * which is required for LESS, GREATER, LEQ, and GEQ. See
	 * {@link PolynomialRelation#constructRhsIntegerQuotient}
	 * @param postDivisionOffset
	 *            value that is added after the division and that is determined from
	 *            the relation symbol and the sign of the divisor's values.
	 */
	private static Term constructRhsIntegerQuotientHelper(final Script script, final Term divident,
			final Rational postDivisionOffset, final Term... divisor) {
		// The preDivisionOffset is always minus one.
		final Term preDivisionOffset = SmtUtils.rational2Term(script, Rational.MONE, divident.getSort());
		final Term divArgument = SmtUtils.sum(script, divident.getSort(), divident, preDivisionOffset);
		final Term simplifiedDivArgument = ((IPolynomialTerm) (new PolynomialTermTransformer(script))
				.transform(divArgument)).toTerm(script);
		final Term[] result = prepend(simplifiedDivArgument, divisor);
		final Term quotient = SmtUtils.division(script, divident.getSort(), result);
		return SmtUtils.sum(script, divident.getSort(), quotient,
				SmtUtils.rational2Term(script, postDivisionOffset, divident.getSort()));
	}

	private static Term[] prepend(final Term head, final Term... tail) {
		final List<Term> resultAsList = new ArrayList<>(tail.length + 1);
		resultAsList.add(head);
		resultAsList.addAll(Arrays.asList(tail));
		final Term[] resultArray = resultAsList.toArray(new Term[resultAsList.size()]);
		return resultArray;
	}

	/**
	 * @return true iff var is variable of this {@link PolynomialRelation}
	 */
	public boolean isVariable(final Term var) {
		return mPolynomialTerm.isVariable(var);
	}

	private boolean divisionByVariablesNecessary(final Term abstractVarOfSubject) {
		if (abstractVarOfSubject instanceof Monomial) {
			return !((Monomial) abstractVarOfSubject).isLinear();
		}
		return false;
	}

	private boolean isEqOrDistinct(final RelationSymbol relSym) {
		return (relSym.equals(RelationSymbol.EQ)) || (relSym.equals(RelationSymbol.DISTINCT));
	}

	private boolean isBvAndCantBeSolved(final Rational coeffOfSubject, final Term abstractVarOfSubject) {
		return SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort()) && (divisionByVariablesNecessary(
				abstractVarOfSubject)
				|| !(coeffOfSubject.equals(Rational.ONE) || isBvMinusOne(coeffOfSubject, mPolynomialTerm.getSort())));
	}

	private boolean isBvMinusOne(final Rational number, final Sort bvSort) {
		final int vecSize = Integer.parseInt(bvSort.getIndices()[0]);
		final BigInteger minusOne = BigInteger.valueOf(2).pow(vecSize).subtract(BigInteger.ONE);
		final Rational rationalMinusOne = Rational.valueOf(minusOne, BigInteger.ONE);
		return number.equals(rationalMinusOne);
	}

	private boolean isNegative(final Rational coeffOfSubject) {
		return coeffOfSubject.isNegative() || (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())
				&& isBvMinusOne(coeffOfSubject, mPolynomialTerm.getSort()));
	}

	/**
	 * Check if subject occurs in exactly one abstract variable. Assumes that
	 * subject is variable of at least one abstract variable (throws AssertionError
	 * otherwise). Returns null if subject occurs in more that one abstract
	 * variable, returns the abstract variable of the subject otherwise.
	 */
	private Term getTheAbstractVarOfSubject(final Term subject) {
		if (mPolynomialTerm.isAffine()) {
			return getVarOfSubject(subject);
		} else {
			return getMonomialOfSubject(subject);
		}
	}

	/**
	 * This implements getAbstractVarOfSubject in case that this Relation represents
	 * a truly polynomial relation.
	 */
	private Term getMonomialOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		Term abstractVarOfSubject = null;
		for (final Term concreteVar : mPolynomialTerm.getAbstractVariable2Coefficient().keySet()) {
			for (final Entry<Term, Rational> var2exp : ((Monomial) concreteVar).getVariable2Exponent().entrySet()) {
				if (var2exp.getKey() == subject) {
					if (var2exp.getValue() != Rational.ONE || subjectOccurred) {
						return null;
					} else {
						subjectOccurred = true;
						abstractVarOfSubject = concreteVar;
					}
				} else {
					final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
							.isPropertySatisfied(var2exp.getKey());
					if (subjectOccursAsSubterm) {
						return null;
					}
				}
			}
		}
		if (!subjectOccurred) {
			throw new AssertionError("superclass already checked that subject is abstract var");
		}
		if (abstractVarOfSubject == null) {
			throw new AssertionError("abstractVarOfSubject must always be assigned, when the subject occurs!");
		}
		return abstractVarOfSubject;
	}

	/**
	 * This implements getAbstractVarOfSubject in case that this is an affine
	 * Relation.
	 */
	private Term getVarOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		Term abstractVarOfSubject = null;
		for (final Term concreteVar : mPolynomialTerm.getAbstractVariable2Coefficient().keySet()) {
			if (concreteVar == subject) {
				subjectOccurred = true;
				abstractVarOfSubject = concreteVar;
			} else {
				final boolean subjectOccursAsSubterm = new SubtermPropertyChecker(x -> x == subject)
						.isPropertySatisfied(concreteVar);
				if (subjectOccursAsSubterm) {
					return null;
				}
			}
		}
		if (!subjectOccurred) {
			throw new AssertionError("superclass already checked that subject is abstract var");
		}
		return abstractVarOfSubject;
	}

	public static PolynomialRelation convert(final Script script, final Term term) {
		return convert(script, term, TransformInequality.NO_TRANFORMATION);
	}

	public static PolynomialRelation convert(final Script script, final Term term,
			final TransformInequality transformInequality) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AbstractGeneralizedAffineTerm<?> polyLhs = transformToPolynomialTerm(script, lhs);
		final AbstractGeneralizedAffineTerm<?> polyRhs = transformToPolynomialTerm(script, rhs);
		if (polyLhs.isErrorTerm() || polyRhs.isErrorTerm()) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		return new PolynomialRelation(script, transformInequality, relationSymbol, polyLhs, polyRhs, term);
	}

	static AbstractGeneralizedAffineTerm<?> transformToPolynomialTerm(final Script script, final Term term) {
		return (AbstractGeneralizedAffineTerm<?>) new PolynomialTermTransformer(script).transform(term);
	}
}
