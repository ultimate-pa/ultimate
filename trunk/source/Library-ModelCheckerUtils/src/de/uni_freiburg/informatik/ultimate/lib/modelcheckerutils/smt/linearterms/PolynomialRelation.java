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
 * {@link PolynomialTerm}s or {@link AffineTerm}s and ▷ is a binary relation symbol
 * from the following list.
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
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the mOriginalTerm.
	 */
	protected final AbstractGeneralizedAffineTerm<Term> mPolynomialTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link PolynomialRelation} from {@link IPolynomialTerm} and {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
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
	 * Given a AbstractGeneralizedAffineTerm, check whether it is of Type AffineTerm and PolynomialTerm.
	 * If yes, cast it (UNSAFE) and return the result, throw an exception otherwise.
	 */
	private static AbstractGeneralizedAffineTerm<Term> checkThenCast(final AbstractGeneralizedAffineTerm<?> poly){
		if (!(poly instanceof AffineTerm || poly instanceof PolynomialTerm)) {
			throw new IllegalArgumentException("PolynomialRelation accepts only AffineTerm "
					+ "and PolynomialTerm as internal terms.");
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
		}
		return TrivialityStatus.EQUIVALENT_TO_FALSE;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public AbstractGeneralizedAffineTerm<Term> getPolynomialTerm() {
		return mPolynomialTerm;
	}

	/**
	 * Returns a term representation of this PolynomialRelation where each summand occurs only positive and the greater-than
	 * relation symbols are replaced by less-than relation symbols. If the term is equivalent to <i>true</i> (resp.
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
					rhsSummands.add(
							SmtUtils.rational2Term(script, mPolynomialTerm.getConstant().abs(), mPolynomialTerm.getSort()));
				} else {
					lhsSummands.add(SmtUtils.rational2Term(script, mPolynomialTerm.getConstant(), mPolynomialTerm.getSort()));
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
	 * Returns a {@link SolvedBinaryRelation} that is equivalent to this PolynomialRelation or null if we cannot find
	 * such a {@link SolvedBinaryRelation}.
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
			rhsTerm = integerDivision(script, coeffOfSubject, rhsTermWithoutDivision);
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
		final Term relationToTerm = result.relationToTerm(script);
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
	 * Returns a {@link MultiCaseSolvedBinaryRelation} that is equivalent to this PolynomialRelation or null if we
	 * cannot find such a {@link MultiCaseSolvedBinaryRelation}.
	 */
	public MultiCaseSolvedBinaryRelation solveForSubject(final Script script, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf) {
		boolean subjectInAllowedSubterm = false;
		ApplicationTerm allowedSubterm = null;
		if (!isVariable(subject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not a variable");
			} else {
				allowedSubterm = searchModOrDivSubterm(mPolynomialTerm.toTerm(script), script, subject);
				if (allowedSubterm != null) {
					subjectInAllowedSubterm = true;
				} else {
					return null;
				}
			}
		}
		Term abstractVarOfSubject = getTheAbstractVarOfSubject(subject);
		if (subjectInAllowedSubterm && (abstractVarOfSubject == null)) {
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
		if (subjectInAllowedSubterm && (coeffOfSubject == null)) {
			final ConstantTerm coeffTerm = (ConstantTerm) allowedSubterm.getParameters()[1];
			coeffOfSubject = SmtUtils.convertConstantTermToRational(coeffTerm);
			// TODO if no constantTErm throw error or handle it
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

		final RelationSymbol resultRelationSymbol;
		if (isNegative(coeffOfSubject)) {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = BinaryRelation.swapParameters(mRelationSymbol);
		} else {
			resultRelationSymbol = mRelationSymbol;
		}

		final Term simplySolvableRhsTerm = constructRhsForAbstractVariable(script, abstractVarOfSubject,
				coeffOfSubject);
		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		Term rhsTerm = null;
		if (simplySolvableRhsTerm == null) {
			if (!subjectInAllowedSubterm) {
				final Term rhsTermWithoutDivision = constructRhsForAbstractVariable(script, abstractVarOfSubject,
						Rational.ONE);
				rhsTerm = integerDivision(script, coeffOfSubject, rhsTermWithoutDivision);
				final SolvedBinaryRelation sbr = new SolvedBinaryRelation(subject, rhsTerm, resultRelationSymbol,
						Collections.emptyMap());
				// EQ and DISTINCT need Modulo Assumption
				if ((mRelationSymbol.equals(RelationSymbol.EQ)) || (mRelationSymbol.equals(RelationSymbol.DISTINCT))) {
					final boolean negate = mRelationSymbol.equals(RelationSymbol.DISTINCT);
					final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script,
							rhsTermWithoutDivision, coeffOfSubject.toTerm(mPolynomialTerm.getSort()), negate);
					final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
							IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
					switch (mRelationSymbol) {
					case DISTINCT:
						if (!divisionByVariablesNecessary(abstractVarOfSubject)) {
							mcsb.conjoinWithDisjunction(sbr, divisibilityConstraint);
						} else {
							mcsb.conjoinWithDisjunction(divisibilityConstraint);
						}
						break;
					case EQ:
						if (!divisionByVariablesNecessary(abstractVarOfSubject)) {
							mcsb.conjoinWithConjunction(sbr, divisibilityConstraint);
						} else {
							mcsb.conjoinWithConjunction(divisibilityConstraint);
						}
						break;
					case GEQ:
					case GREATER:
					case LEQ:
					case LESS:
					default:
						throw new AssertionError("cases not handled here");
					}
				} else {
					// cases LEQ, LESS, GREATER, GEQ: do not add SupportingTerm
					if (!divisionByVariablesNecessary(abstractVarOfSubject)) {
						mcsb.conjoinWithConjunction(sbr);
					}
					// we have to add this information separately because
					// there is no SupporingTerm that provides this information
					mcsb.reportAdditionalIntricateOperation(IntricateOperation.DIV_BY_INTEGER_CONSTANT);
				}
			} else if (subjectInAllowedSubterm) {
				// Solve for subject in affineterm with a parameter of form (mod/div (subterm with subject) constant)
				final Sort termSort = mPolynomialTerm.getSort();
				// recVarName ensures different names in each recursion, since AffineRelation is made new each time
				final int recVarName = allowedSubterm.toString().length();
				final TermVariable auxDiv = script.variable("aux_div_" + recVarName, termSort);
				final TermVariable auxMod = script.variable("aux_mod_" + recVarName, termSort);

				final Term multiplication = SmtUtils.mul(script, termSort,
						SmtUtils.rational2Term(script, coeffOfSubject, termSort), auxDiv);
				final Term sum = SmtUtils.sum(script, termSort, auxMod, multiplication);

				final AbstractGeneralizedAffineTerm recursion = (AbstractGeneralizedAffineTerm) new AffineTermTransformer(script)
						.transform(allowedSubterm.getParameters()[0]);
				if (!recursion.isVariable(subject)) {
					// recursiv call for terms of form: "(mod ...(mod subject const1)... const 2)"
					final MultiCaseSolvedBinaryRelation mcsbr = PolynomialRelation
							.convert(script, SmtUtils.binaryEquality(script, allowedSubterm.getParameters()[0], sum))
							.solveForSubject(script, subject, xnf);
					final SupportingTerm recSupTerm = new SupportingTerm(mcsbr.asTerm(script),
							IntricateOperation.MUL_BY_INTEGER_CONSTANT, mcsbr.getAuxiliaryVariables());
					mcsb.conjoinWithConjunction(recSupTerm);
				} else {
					// solve terms of form (mod (subterm) const) where subterm contains x but is no mod or div term
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
			}
		} else {
			rhsTerm = simplySolvableRhsTerm;
			if (!divisionByVariablesNecessary(abstractVarOfSubject)) {
				final SolvedBinaryRelation sbr = new SolvedBinaryRelation(subject, rhsTerm, resultRelationSymbol,
						Collections.emptyMap());
				mcsb.conjoinWithConjunction(sbr);
			}
		}
		if (divisionByVariablesNecessary(abstractVarOfSubject)) {
			// TODO 13.11.2019: When we divide by variables we could actually sometimes simplify the resulting division,
			// in the case that this variable is not zero (and therefore we can simplify f.ex. x/x to 1).
			// Also we could sometimes get Conjuncts like x!=0, that are already in the case distinction.
			// Handle this in the MultiCaseSolutionBuilder?
			// At the moment this seems like much work relative to little effect, so I was asked to leave this comment
			// here for the future.
			final Collection<Case> finishedCases = new ArrayList<>();
			Collection<IntermediateCase> previousCases = new ArrayList<>();
			Collection<IntermediateCase> nextCases = new ArrayList<>();

			final Set<SupportingTerm> supp = Collections.emptySet();
			final IntermediateCase startCase = new IntermediateCase(supp, MultiCaseSolvedBinaryRelation.Xnf.DNF,
					rhsTerm, resultRelationSymbol);
			previousCases.add(startCase);

			for (final Entry<Term, Rational> var2exp : ((Monomial) abstractVarOfSubject).getVariable2Exponent()
					.entrySet()) {
				if (var2exp.getKey() == subject) {
					// do nothing
				} else {
					for (final IntermediateCase previousCase : previousCases) {
						finishedCases.add(constructDivByVarEqualZeroCase(script, previousCase, var2exp.getKey()));
						assert var2exp.getValue().isIntegral();
						final int exp = var2exp.getValue().numerator().intValueExact();
						if (isEqOrDistinct(mRelationSymbol) || exp % 2 == 0) {
							nextCases.add(constructDivByVarDistinctZeroCase(script, previousCase, var2exp));
						} else {
							//We have to distinguish the case now into two cases,
							//since the RelationSymbol has to be swapped, when we divide by a negative variable.
							nextCases.add(constructDivByVarLessZeroCase(script, previousCase, var2exp));
							nextCases.add(constructDivByVarGreaterZeroCase(script, previousCase, var2exp));
						}
					}
					previousCases = nextCases;
					nextCases = new ArrayList<>();
				}
			}
			for (final IntermediateCase finishedCase : previousCases) {
				finishedCases.add(finishedCase.finalizeCase(subject));
			}
			final Collection<Collection<?>> dnf = new ArrayList<>();
			for (final Case c : finishedCases) {
				dnf.add(transformCaseIntoCollection(c));
			}
			mcsb.conjoinWithDnf(dnf);
		}

		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		if (!subjectInAllowedSubterm) {
			assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
					result.asTerm(script)) != LBool.SAT : "solveForSubject unsound";
		}
		return result;
	}

	/**
	 * go thru the parameters of the affineTerm and search for a term of form (mod subterm const) or (div subterm const)
	 * where subterm contains the subject
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

	private static Term constructDivisibilityConstraint(final Script script, final Term divident, final Term divisor,
			final boolean negate) {
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

	private Case constructDivByVarEqualZeroCase(final Script script, final IntermediateCase previousCase,
			final Term var) {
		final RelationSymbol relSym = previousCase.getIntermediateRelationSymbol();
		final Term rhs = previousCase.getIntermediateRhs();
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>(previousCase.getSupportingTerms());
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, mPolynomialTerm.getSort());
		final Term varEqualZero = SmtUtils.binaryEquality(script, zeroTerm, var);
		suppTerms.add(new SupportingTerm(varEqualZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		final Term rhsRelationZeroTerm;
		switch(relSym) {
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
			throw new UnsupportedOperationException("No such RelationSymbol known.");
		}
		suppTerms.add(
				new SupportingTerm(rhsRelationZeroTerm, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet()));
		return new Case(null, suppTerms, MultiCaseSolvedBinaryRelation.Xnf.DNF);
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
	 * Try to bring everything but abstractVarOfSubject to the right-hand side. Try to divide the coefficient of every
	 * other variable and the constant by the coeffOfAbstractVar. If the sort is not real and for some coefficient the
	 * quotient is not integral return null. Otherwise return the {@link Term} representation of the right-hand side.
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
					//This only works because we know that in our cases coeffOfAbstractVar is always
					//its own multiplicative inverse.
					newCoeff = entry.getValue().mul(coeffOfAbstractVar);
				}else {
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
				//This only works because we know that in our cases coeffOfAbstractVar is always
				//its own multiplicative inverse.
				newConstant = mPolynomialTerm.getConstant().mul(coeffOfAbstractVar);
			}else {
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

	private Term integerDivision(final Script script, final Rational coeffOfSubject,
			final Term rhsTermWithoutDivision) {
		// Default DivTerm
		final Term divTerm;
		// change DivTerm according to the given relation symbol
		switch (mRelationSymbol) {
		case LESS:
			if (!coeffOfSubject.isNegative()) {
				// k*x < t is equivalent to x < (t-1 div k)+1 for positive k
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.ONE);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.MONE);
			}
			break;
		case GREATER:
			// k*x > t is equivalent to x > (t div k) for all k
			divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mPolynomialTerm.getSort()));
			break;
		case LEQ:
			// k*x <= t is equivalent to x <= (t div k) for positive k
			divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mPolynomialTerm.getSort()));
			break;
		case GEQ:
			if (!coeffOfSubject.isNegative()) {
				// k*x >= t is equivalent to x >= (t - 1 div k) + 1 for positive k
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.ONE);
			} else {
				// -k*x >= t is equivalent to x <= (t - 1 div -k) - 1
				divTerm = constructDivTerm(script, rhsTermWithoutDivision, coeffOfSubject, Rational.MONE);
			}
			break;
		case EQ:
			// Default DivTerm with modulo Assumption
			divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mPolynomialTerm.getSort()));
			break;
		case DISTINCT:
			// Default DivTerm with modulo Assumption
			divTerm = SmtUtils.div(script, rhsTermWithoutDivision, coeffOfSubject.toTerm(mPolynomialTerm.getSort()));
			break;
		default:
			throw new AssertionError("unknown relation symbol: " + mRelationSymbol);
		}
		return divTerm;
	}

	/*
	 * construct DivTerm for LESS and GEQ case, where the default divTerm can't be used. "secondRat" depends on the sign
	 * of the coefficient.
	 */
	private Term constructDivTerm(final Script script, final Term rhsTermWithoutDivision, final Rational coeffOfSubject,
			final Rational secondRat) {
		final Term divArgument = SmtUtils.sum(script, mPolynomialTerm.getSort(), rhsTermWithoutDivision,
				SmtUtils.rational2Term(script, Rational.MONE, mPolynomialTerm.getSort()));
		final Term simplifiedDivArgument = ((IPolynomialTerm) (new PolynomialTermTransformer(script))
				.transform(divArgument)).toTerm(script);
		final Term divTerm = SmtUtils.div(script, simplifiedDivArgument,
				SmtUtils.rational2Term(script, coeffOfSubject, mPolynomialTerm.getSort()));
		return SmtUtils.sum(script, mPolynomialTerm.getSort(), divTerm,
				SmtUtils.rational2Term(script, secondRat, mPolynomialTerm.getSort()));
	}

	/**
	 * @return true iff var is variable of this {@link PolynomialRelation}
	 */
	public boolean isVariable(final Term var) {
		return mPolynomialTerm.isVariable(var);
	}

	private boolean divisionByVariablesNecessary(final Term abstractVarOfSubject) {
		if(abstractVarOfSubject instanceof Monomial) {
			return !((Monomial) abstractVarOfSubject).isLinear();
		}
		return false;
	}

	private boolean isEqOrDistinct(final RelationSymbol relSym) {
		return (relSym.equals(RelationSymbol.EQ)) || (relSym.equals(RelationSymbol.DISTINCT));
	}

	private boolean isBvAndCantBeSolved(final Rational coeffOfSubject, final Term abstractVarOfSubject) {
		return  SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())
				&& (divisionByVariablesNecessary(abstractVarOfSubject)
						|| !(coeffOfSubject.equals(Rational.ONE)
								|| isBvMinusOne(coeffOfSubject, mPolynomialTerm.getSort())));
	}

	private boolean isBvMinusOne(final Rational number, final Sort bvSort) {
		final int vecSize = Integer.valueOf(bvSort.getIndices()[0]).intValue();
		final BigInteger minusOne = new BigInteger("2").pow(vecSize).subtract(BigInteger.ONE);
		final Rational rationalMinusOne = Rational.valueOf(minusOne, BigInteger.ONE);
		return number.equals(rationalMinusOne);
	}

	private boolean isNegative(final Rational coeffOfSubject) {
		return coeffOfSubject.isNegative()
				|| (SmtSortUtils.isBitvecSort(mPolynomialTerm.getSort())
						&& isBvMinusOne(coeffOfSubject, mPolynomialTerm.getSort()));
	}

	/**
	 * Check if subject occurs in exactly one abstract variable. Assumes that subject is variable of at least one
	 * abstract variable (throws AssertionError otherwise). Returns null if subject occurs in more that one abstract
	 * variable, returns the abstract variable of the subject otherwise.
	 */
	private Term getTheAbstractVarOfSubject(final Term subject) {
		if (mPolynomialTerm.isAffine()) {
			return getVarOfSubject(subject);
		}else {
			return getMonomialOfSubject(subject);
		}
	}

	/**
	 * This implements getAbstractVarOfSubject in case that this Relation represents a truly polynomial relation.
	 */
	private Term getMonomialOfSubject(final Term subject) {
		boolean subjectOccurred = false;
		Term abstractVarOfSubject = null;
		for (final Term concreteVar : mPolynomialTerm.getAbstractVariable2Coefficient().keySet()) {
			for (final Entry<Term, Rational> var2exp : ((Monomial) concreteVar).getVariable2Exponent().entrySet()) {
				if (var2exp.getKey() == subject) {
					if (var2exp.getValue() != Rational.ONE || subjectOccurred) {
						return null;
					}else {
						subjectOccurred = true;
						abstractVarOfSubject = concreteVar;
					}
				}else {
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
	 * This implements getAbstractVarOfSubject in case that this is an affine Relation.
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
