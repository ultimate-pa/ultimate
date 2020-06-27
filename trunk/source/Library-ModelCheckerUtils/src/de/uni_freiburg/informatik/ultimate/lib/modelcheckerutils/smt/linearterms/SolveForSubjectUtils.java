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
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsSubterm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.Case;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolutionBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
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

/**
 * Auxiliary methods for {@link PolynomialRelation#solveForSubject}
 *
 * @author Leonard Fichtner
 * @author Max Barth
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SolveForSubjectUtils {

	private static final boolean THROW_EXCEPTION_IF_NOT_SOLVABLE = false;

	static SolvedBinaryRelation solveForSubject(final Script script, final Term subject,
			final PolynomialRelation polyRel) {
		if (!polyRel.isVariable(subject)) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject is not a variable");
			} else {
				return null;
			}
		}
		final Monomial monomialOfSubject = polyRel.getPolynomialTerm().getExclusiveMonomialOfSubject(subject);
		if (monomialOfSubject == null) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("subject occurs in several abstract variables");
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
		if (!monomialOfSubject.isLinear()) {
			if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
				throw new UnsupportedOperationException("Division by variables needs case distinction");
			} else {
				return null;
			}
		}
		final Rational coeffOfSubject;
		if (polyRel.getPolynomialTerm().isAffine()) {
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient()
					.get(monomialOfSubject.getVariable2Exponent().keySet().iterator().next());
		} else {
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(monomialOfSubject);
		}

		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}
		if (isBvAndCantBeSolved(coeffOfSubject, monomialOfSubject)) {
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

		final Term simpliySolvableRhsTerm = constructRhsForMonomial(script, monomialOfSubject, coeffOfSubject,
				polyRel.getPolynomialTerm());
		final AssumptionMapBuilder assumptionMapBuilder = new AssumptionMapBuilder(script);
		Term rhsTerm;
		if (simpliySolvableRhsTerm == null) {
			final Term rhsTermWithoutDivision = constructRhsForMonomial(script, monomialOfSubject, Rational.ONE,
					polyRel.getPolynomialTerm());
			rhsTerm = constructRhsIntegerQuotient(script, polyRel.getRelationSymbol(), rhsTermWithoutDivision,
					!coeffOfSubject.isNegative(), coeffOfSubject.toTerm(rhsTermWithoutDivision.getSort()));
			// EQ and DISTINCT need Modulo Assumption
			if (isEqOrDistinct(polyRel.getRelationSymbol())) {
				assumptionMapBuilder.putDivisibleByConstant(rhsTermWithoutDivision,
						coeffOfSubject.toTerm(subject.getSort()));
			}
			// cases LEQ, LESS, GREATER, GEQ do nothing

		} else {
			rhsTerm = simpliySolvableRhsTerm;
		}

		final RelationSymbol resultRelationSymbol;
		if (isNegative(coeffOfSubject, subject.getSort())) {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = polyRel.getRelationSymbol().swapParameters();
		} else {
			resultRelationSymbol = polyRel.getRelationSymbol();
		}

		final SolvedBinaryRelation result = new SolvedBinaryRelation(subject, rhsTerm, resultRelationSymbol,
				assumptionMapBuilder.getExplicitAssumptionMap());
		final Term relationToTerm = result.asTerm(script);
		if (!assumptionMapBuilder.isEmpty()) {
			assert script instanceof INonSolverScript || assumptionImpliesEquivalence(script,
					polyRel.positiveNormalForm(script), relationToTerm, assumptionMapBuilder
							.getExplicitAssumptionMap()) != LBool.SAT : "transformation to AffineRelation unsound";
		} else {
			assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(polyRel.positiveNormalForm(script),
					relationToTerm, script) != LBool.SAT : "transformation to AffineRelation unsound";
		}
		return result;
	}

	static MultiCaseSolvedBinaryRelation solveForSubject(final Script script, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final PolynomialRelation polyRel) throws AssertionError {
		MultiCaseSolvedBinaryRelation res = findTreatableDivModSubterm(script, subject, polyRel.getPolynomialTerm(),
				null, xnf, polyRel.positiveNormalForm(script));
		if (res == null) {
			res = solveForSubjectWithoutTreatableDivMod(script, subject, polyRel, xnf);
		}
		if (res == null) {
			return null;
		}
		assert res.isSubjectOnlyOnRhs() : "subject not only LHS";
		assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(polyRel.positiveNormalForm(script),
				res.asTerm(script), script) != LBool.SAT : "solveForSubject unsound";
		return res;
	}

	private static MultiCaseSolvedBinaryRelation solveForSubjectWithoutTreatableDivMod(final Script script,
			final Term subject, final PolynomialRelation polyRel, final MultiCaseSolvedBinaryRelation.Xnf xnf)
			throws AssertionError {

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
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient()
					.get(monomialOfSubject.getVariable2Exponent().keySet().iterator().next());
		} else {
			coeffOfSubject = polyRel.getPolynomialTerm().getAbstractVariable2Coefficient().get(monomialOfSubject);
		}
		if (coeffOfSubject.equals(Rational.ZERO)) {
			throw new AssertionError("no abstract variable must have coefficient zero");
		}
		if (isBvAndCantBeSolved(coeffOfSubject, monomialOfSubject)) {
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
		final boolean isOriginalCoefficientPositive = !isNegative(coeffOfSubject, subject.getSort());
		{
			final Term simplySolvableRhsTerm = constructRhsForMonomial(script, monomialOfSubject, coeffOfSubject,
					polyRel.getPolynomialTerm());
			if (simplySolvableRhsTerm == null) {
				stageTwoRhs = constructRhsForMonomial(script, monomialOfSubject, Rational.ONE,
						polyRel.getPolynomialTerm());
				stageTwoCoefficient = coeffOfSubject;
			} else {
				stageTwoRhs = simplySolvableRhsTerm;
				stageTwoCoefficient = null;
			}
		}
		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		final Collection<Case> cases = new ArrayList<>();
		final Term[] divisorAsArray;
		if (!monomialOfSubject.isLinear()) {
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
				divisorAsList.add(stageTwoCoefficient.toTerm(subject.getSort()));
			}
			for (final Entry<Term, Rational> var2exp : monomialOfSubject.getVariable2Exponent().entrySet()) {
				assert var2exp.getValue().isIntegral();
				if (var2exp.getKey() == subject) {
					// do nothing
				} else {
					cases.add(constructDivByVarEqualZeroCase(script, var2exp.getKey(), stageTwoRhs,
							polyRel.getRelationSymbol(), xnf));
					final int exp = var2exp.getValue().numerator().intValueExact();
					for (int i = 0; i < exp; i++) {
						divisorAsList.add(var2exp.getKey());
					}
					if (isEqOrDistinct(polyRel.getRelationSymbol()) || exp % 2 == 0) {
						twoCaseVariables.add(var2exp.getKey());
						distinctZeroSupportingTerms.add(constructInRelationToZeroSupportingTerm(script,
								var2exp.getKey(), negateForCnf(RelationSymbol.DISTINCT, xnf)));
					} else {
						// We have to distinguish the case now into two cases,
						// since the RelationSymbol has to be swapped, when we divide by a negative
						// variable.
						threeCaseVariables.add(var2exp.getKey());
						isNegativeSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(),
								negateForCnf(RelationSymbol.LESS, xnf)));
						isPositiveSupportingTerms.add(constructInRelationToZeroSupportingTerm(script, var2exp.getKey(),
								negateForCnf(RelationSymbol.GREATER, xnf)));
					}
				}
			}
			divisorAsArray = divisorAsList.toArray(new Term[divisorAsList.size()]);
			// final Term resultRhs = SmtUtils.division(script, rhsTerm.getSort(),
			// divisorAsList.toArray(new Term[divisorAsList.size()]));
			if (threeCaseVariables.isEmpty()) {
				final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs,
						polyRel.getRelationSymbol(), isOriginalCoefficientPositive, divisorAsArray);
				final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
				if (isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(), polyRel.getRelationSymbol())) {
					final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
							stageTwoRhs, polyRel.getRelationSymbol(), divisorAsArray);
					thisCaseSupportingTerms.add(divisibilityConstraint);
				}
				cases.add(new Case(sbr, thisCaseSupportingTerms, xnf));
			} else {
				if (threeCaseVariables.size() > 30) {
					throw new UnsupportedOperationException(
							"Exponential blowup too huge. Exponent is " + threeCaseVariables.size());
				}
				final int numberOfCases = BigInteger.valueOf(2).pow(threeCaseVariables.size()).intValueExact();
				for (int i = 0; i < numberOfCases; i++) {
					// if bit is set this means that we assume that variable is negative
					final boolean isDivisorPositive = ((BigInteger.valueOf(i).bitCount()
							% 2 == 0) == isOriginalCoefficientPositive);
					final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs,
							polyRel.getRelationSymbol(), isDivisorPositive, divisorAsArray);
					final Set<SupportingTerm> thisCaseSupportingTerms = new HashSet<>(distinctZeroSupportingTerms);
					for (int j = 0; j < threeCaseVariables.size(); j++) {
						SupportingTerm posOrNegSupportingTerm;
						if (BigInteger.valueOf(i).testBit(j)) {
							posOrNegSupportingTerm = isNegativeSupportingTerms.get(j);
						} else {
							posOrNegSupportingTerm = isPositiveSupportingTerms.get(j);
						}
						thisCaseSupportingTerms.add(posOrNegSupportingTerm);
					}
					if (isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(),
							polyRel.getRelationSymbol())) {
						final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
								stageTwoRhs, polyRel.getRelationSymbol(), divisorAsArray);
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
				divisorAsArray = new Term[] { stageTwoCoefficient.toTerm(subject.getSort()) };
			}
			final SolvedBinaryRelation sbr = constructSolvedBinaryRelation(script, subject, stageTwoRhs,
					polyRel.getRelationSymbol(), isDivisorPositive, divisorAsArray);
			final Set<SupportingTerm> supportingTerms;
			if (stageTwoCoefficient != null && isDerIntegerDivisionSupportingTermRequired(xnf, subject.getSort(),
					polyRel.getRelationSymbol())) {
				final SupportingTerm divisibilityConstraint = constructDerIntegerDivisionSupportingTerm(script,
						stageTwoRhs, polyRel.getRelationSymbol(), divisorAsArray);
				supportingTerms = Collections.singleton(divisibilityConstraint);
			} else {
				supportingTerms = Collections.emptySet();
			}
			cases.add(new Case(sbr, supportingTerms, xnf));
		}
		if (isAntiDerIntegerDivisionCaseRequired(xnf, subject.getSort(), polyRel.getRelationSymbol())) {
			final Case result = constructAntiDerIntegerDivisibilityCase(script, xnf, stageTwoRhs,
					polyRel.getRelationSymbol(), divisorAsArray);
			cases.add(result);
		}
		mcsb.splitCases(cases);

		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		return result;
	}

	private static MultiCaseSolvedBinaryRelation tryToHandleDivModSubterm(final Script script, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final ApplicationTerm divModSubterm, final Term pnf) {
		final Term divisor = SmtUtils.mul(script, "*",
				Arrays.copyOfRange(divModSubterm.getParameters(), 1, divModSubterm.getParameters().length));
		assert (divisor instanceof ConstantTerm) : "not constant";
		// Solve for subject in affineterm with a parameter of form (mod/div (subterm
		// with subject) constant)
		final Sort termSort = subject.getSort();
		// recVarName ensures different names in each recursion, since AffineRelation is
		// made new each time
		final int recVarName = divModSubterm.toString().length();
		final TermVariable auxDiv = script.variable("aux_div_" + recVarName, termSort);
		final TermVariable auxMod = script.variable("aux_mod_" + recVarName, termSort);

		final MultiCaseSolvedBinaryRelation solvedComparison;

		{
			final Term multiplication = SmtUtils.mul(script, termSort, divisor, auxDiv);
			final Term sum = SmtUtils.sum(script, termSort, auxMod, multiplication);
			final Term subtermSumComparison = BinaryRelation.toTerm(script, negateForCnf(RelationSymbol.EQ, xnf),
					divModSubterm.getParameters()[0], sum);
			// recursive call for (= divident[subject] (+ (* aux_div divisor) aux_mod))
			solvedComparison = PolynomialRelation.convert(script, subtermSumComparison).solveForSubject(script, subject,
					xnf);
			if (solvedComparison == null) {
				return null;
			}
		}

		final MultiCaseSolutionBuilder mcsb = new MultiCaseSolutionBuilder(subject, xnf);
		// construct as SupportingTerm either
		// (= (div divident[subject] divisor) aux_div) or
		// (= (mod divident[subject] divisor) mod_div)
		final Set<TermVariable> setAuxVars = new HashSet<>();
		// substitute allowedSubterm with corresponding aux variable in input
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		if (SmtUtils.isIntMod(divModSubterm)) {
			substitutionMapping.put(divModSubterm, auxMod);
			setAuxVars.add(auxMod);
			mcsb.reportAdditionalAuxiliaryVariable(auxDiv);
		} else if (SmtUtils.isIntDiv(divModSubterm)) {
			setAuxVars.add(auxDiv);
			substitutionMapping.put(divModSubterm, auxDiv);
		} else {
			throw new AssertionError("input must be div or mod");
		}
		final List<Case> resultCases = new ArrayList<>();
		for (final Case c : solvedComparison.getCases()) {
			if (c.getSolvedBinaryRelation() != null) {
				substitutionMapping.put(subject, c.getSolvedBinaryRelation().getRightHandSide());
			}
			final Term auxModEqualsTerm = new Substitution(script, substitutionMapping).transform(pnf);
			if (c.getSolvedBinaryRelation() == null) {
				final boolean containsSubject = new ContainsSubterm(subject).containsSubterm(auxModEqualsTerm);
				if (containsSubject) {
					// cannot solve, one Case has no SolvedBinaryRelation and the PolynomialRelation
					// contains the subject also outside the considered div/mod term.
					// TODO 20200612 Matthias: Optimization: Try to solve differently for this
					// case and use the other occurrence of the subject.
					// Complicated, but probably not yet relevant in practice.
					return null;
				}
			}
			final SupportingTerm auxEquals = new SupportingTerm(auxModEqualsTerm,
					IntricateOperation.MUL_BY_INTEGER_CONSTANT, new HashSet<>(setAuxVars));
			final Set<SupportingTerm> resultSupportingTerms = new HashSet<>(c.getSupportingTerms());
			resultSupportingTerms.add(auxEquals);
			final Case resultCase = new Case(c.getSolvedBinaryRelation(), resultSupportingTerms, xnf);
			resultCases.add(resultCase);
		}

		mcsb.splitCases(resultCases);
		for (final TermVariable add : solvedComparison.getAuxiliaryVariables()) {
			mcsb.reportAdditionalAuxiliaryVariable(add);
		}
		for (final IntricateOperation add : solvedComparison.getIntricateOperations()) {
			mcsb.reportAdditionalIntricateOperation(add);
		}

		setAuxVars.add(auxMod);

		// construct SupportingTerm (0<=aux_mod)
		final Term auxModGreaterZeroTerm = BinaryRelation.toTerm(script, negateForCnf(RelationSymbol.LEQ, xnf),
				Rational.ZERO.toTerm(termSort), auxMod);
		final SupportingTerm auxModGreaterZero = new SupportingTerm(auxModGreaterZeroTerm,
				IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

		// construct SupportingTerm (aux_mod < k)
		final Term auxModLessCoefTerm = BinaryRelation.toTerm(script, negateForCnf(RelationSymbol.LESS, xnf), auxMod,
				divisor);
		final SupportingTerm auxModLessCoef = new SupportingTerm(auxModLessCoefTerm,
				IntricateOperation.MUL_BY_INTEGER_CONSTANT, setAuxVars);

		mcsb.addAtoms(auxModLessCoef, auxModGreaterZero);
		final MultiCaseSolvedBinaryRelation result = mcsb.buildResult();
		assert result.isSubjectOnlyOnRhs() : "subject not only LHS";
		assert script instanceof INonSolverScript || SmtUtils.checkEquivalence(pnf, result.asTerm(script),
				script) != LBool.SAT : "solveForSubject unsound";
		return result;
	}

	/**
	 * Try to bring everything but monomialOfSubject to the right-hand side. Try to
	 * divide the coefficient of every other variable and the constant by the
	 * coeffOfMonomial. If the sort is not real and for some coefficient the
	 * quotient is not integral return null. Otherwise return the {@link Term}
	 * representation of the right-hand side.
	 *
	 * @param polynomialTerm
	 */
	private static Term constructRhsForMonomial(final Script script, final Monomial monomialOfSubject,
			final Rational coeffOfMonomial, final AbstractGeneralizedAffineTerm<Term> polynomialTerm) {
		final Term abstractVarOfSubject;
		if (polynomialTerm.isAffine()) {
			abstractVarOfSubject = monomialOfSubject.getVariable2Exponent().keySet().iterator().next();
		} else {
			abstractVarOfSubject = monomialOfSubject;
		}
		final List<Term> rhsSummands = new ArrayList<>(polynomialTerm.getAbstractVariable2Coefficient().size());
		for (final Entry<Term, Rational> entry : polynomialTerm.getAbstractVariable2Coefficient().entrySet()) {
			if (abstractVarOfSubject == entry.getKey()) {
				// do nothing
			} else {
				final Rational newCoeff;
				if (SmtSortUtils.isBitvecSort(polynomialTerm.getSort())) {
					// This only works because we know that in our cases coeffOfAbstractVar is
					// always
					// its own multiplicative inverse.
					newCoeff = entry.getValue().mul(coeffOfMonomial);
				} else {
					newCoeff = entry.getValue().div(coeffOfMonomial);
				}
				if (newCoeff.isIntegral() || SmtSortUtils.isRealSort(polynomialTerm.getSort())) {
					if (entry.getKey() instanceof Monomial) {
						rhsSummands.add(
								SmtUtils.mul(script, newCoeff.negate(), ((Monomial) entry.getKey()).toTerm(script)));
					} else {
						rhsSummands.add(SmtUtils.mul(script, newCoeff.negate(), entry.getKey()));
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
		if (!polynomialTerm.getConstant().equals(Rational.ZERO)) {
			final Rational newConstant;
			if (SmtSortUtils.isBitvecSort(polynomialTerm.getSort())) {
				// This only works because we know that in our cases coeffOfAbstractVar is
				// always
				// its own multiplicative inverse.
				newConstant = polynomialTerm.getConstant().mul(coeffOfMonomial);
			} else {
				newConstant = polynomialTerm.getConstant().div(coeffOfMonomial);
			}
			if (newConstant.isIntegral() || SmtSortUtils.isRealSort(polynomialTerm.getSort())) {
				rhsSummands.add(SmtUtils.rational2Term(script, newConstant.negate(), polynomialTerm.getSort()));
			} else {
				if (THROW_EXCEPTION_IF_NOT_SOLVABLE) {
					throw new UnsupportedOperationException("some constant not divisible by coefficient of subject");
				} else {
					return null;
				}
			}
		}
		final Term rhsTerm = SmtUtils.sum(script, polynomialTerm.getSort(),
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
	private static Term constructRhsIntegerQuotient(final Script script, final RelationSymbol relSymb, final Term rhs,
			final boolean divisorIsPositive, final Term... divisor) {
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
	 *
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
	 * @return true iff all params starting from index 1 are {@link ConstantTerm}s.
	 */
	public static boolean tailIsConstant(final List<Term> parameters) {
		assert parameters.size() > 1;
		final Iterator<Term> it = parameters.iterator();
		it.next();
		while (it.hasNext()) {
			if (!(it.next() instanceof ConstantTerm)) {
				return false;
			}
		}
		return true;
	}

	private static RelationSymbol negateForCnf(final RelationSymbol symb, final Xnf xnf) {
		if (xnf == Xnf.CNF) {
			return symb.negate();
		} else {
			return symb;
		}
	}

	private static boolean isDerIntegerDivisionSupportingTermRequired(final Xnf xnf, final Sort sort,
			final RelationSymbol relSymb) {
		return SmtSortUtils.isIntSort(sort) && ((relSymb == RelationSymbol.EQ) && xnf == Xnf.DNF
				|| (relSymb == RelationSymbol.DISTINCT) && xnf == Xnf.CNF);
	}

	private static SupportingTerm constructDerIntegerDivisionSupportingTerm(final Script script, final Term stageTwoRhs,
			final RelationSymbol relSymb, final Term[] divisorAsArray) {
		final boolean negate = relSymb.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script, negate, stageTwoRhs,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
		return divisibilityConstraint;
	}

	private static boolean isAntiDerIntegerDivisionCaseRequired(final Xnf xnf, final Sort sort,
			final RelationSymbol relSymb) {
		return SmtSortUtils.isIntSort(sort) && ((relSymb == RelationSymbol.DISTINCT) && xnf == Xnf.DNF
				|| (relSymb == RelationSymbol.EQ) && xnf == Xnf.CNF);
	}

	private static Case constructAntiDerIntegerDivisibilityCase(final Script script,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Term stageTwoRhs, final RelationSymbol relSymb,
			final Term[] divisorAsArray) {
		final Set<SupportingTerm> suppTerms = new HashSet<>();
		final boolean negate = relSymb.equals(RelationSymbol.DISTINCT);
		final Term divisibilityConstraintTerm = constructDivisibilityConstraint(script, negate, stageTwoRhs,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray));
		final SupportingTerm divisibilityConstraint = new SupportingTerm(divisibilityConstraintTerm,
				IntricateOperation.DIV_BY_INTEGER_CONSTANT, Collections.emptySet());
		suppTerms.add(divisibilityConstraint);
		final SupportingTerm inRelationToZero = constructInRelationToZeroSupportingTerm(script,
				SmtUtils.mul(script, stageTwoRhs.getSort(), divisorAsArray),
				negateForCnf(RelationSymbol.DISTINCT, xnf));
		suppTerms.add(inRelationToZero);
		final Case result = new Case(null, suppTerms, xnf);
		return result;
	}

	private static SupportingTerm constructInRelationToZeroSupportingTerm(final Script script, final Term term,
			final RelationSymbol relSym) {
		final Term zero = SmtUtils.rational2Term(script, Rational.ZERO, term.getSort());
		final Term termRelZero = script.term(relSym.toString(), term, zero);
		return new SupportingTerm(termRelZero, IntricateOperation.DIV_BY_NONCONSTANT, Collections.emptySet());
	}

	private static SolvedBinaryRelation constructSolvedBinaryRelation(final Script script, final Term subject,
			final Term stageTwoRhs, final RelationSymbol relSymb, final boolean isDivisorPositive,
			final Term[] divisor) {
		final Term resultRhs;
		if (divisor.length == 0) {
			resultRhs = stageTwoRhs;
		} else {
			if (SmtSortUtils.isIntSort(stageTwoRhs.getSort())) {
				resultRhs = constructRhsIntegerQuotient(script, relSymb, stageTwoRhs, isDivisorPositive, divisor);
			} else {
				resultRhs = SmtUtils.divReal(script, prepend(stageTwoRhs, divisor));
			}
		}
		final RelationSymbol resultRelationSymbol;
		if (isDivisorPositive) {
			resultRelationSymbol = relSymb;
		} else {
			// if coefficient is negative we have to use the "swapped" RelationSymbol
			resultRelationSymbol = relSymb.swapParameters();
		}
		final SolvedBinaryRelation sbr = new SolvedBinaryRelation(subject, resultRhs, resultRelationSymbol,
				Collections.emptyMap());
		return sbr;
	}

	/**
	 * TODO: (1) Documentation (2) Max has an optimization for nested mod terms with
	 * similar divisor, maybe we should simplify such terms in advance or here
	 *
	 * @param xnf
	 * @param term
	 *
	 */
	private static MultiCaseSolvedBinaryRelation findTreatableDivModSubterm(final Script script, final Term subject,
			final IPolynomialTerm divident, final ApplicationTerm parentDivModTerm, final Xnf xnf,
			final Term relationInPnf) {
		for (final Monomial m : divident.getMonomial2Coefficient().keySet()) {
			for (final Term abstractVariable : m.getVariable2Exponent().keySet()) {
				if (SmtUtils.isIntDiv(abstractVariable) || SmtUtils.isIntMod(abstractVariable)) {
					final ApplicationTerm appTerm = (ApplicationTerm) abstractVariable;
					final boolean dividentContainsSubject = new ContainsSubterm(subject)
							.containsSubterm(appTerm.getParameters()[0]);
					final boolean tailIsConstant = tailIsConstant(Arrays.asList(appTerm.getParameters()));
					if (dividentContainsSubject) {
						final IPolynomialTerm innerDivident = (IPolynomialTerm) new PolynomialTermTransformer(script)
								.transform(appTerm.getParameters()[0]);
						final ApplicationTerm suiteableDivModParent;
						if (tailIsConstant) {
							suiteableDivModParent = appTerm;
						} else {
							suiteableDivModParent = null;
						}
						final MultiCaseSolvedBinaryRelation rec = findTreatableDivModSubterm(script, subject,
								innerDivident, suiteableDivModParent, xnf, relationInPnf);
						if (rec != null) {
							return rec;
						}
					}
				}
			}
		}
		if (parentDivModTerm == null) {
			return null;
		}
		return tryToHandleDivModSubterm(script, subject, xnf, parentDivModTerm, relationInPnf);
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

	private static Case constructDivByVarEqualZeroCase(final Script script, final Term divisorVar, final Term rhs,
			final RelationSymbol relSym, final Xnf xnf) {
		final Set<SupportingTerm> suppTerms = new LinkedHashSet<>();
		final Term zeroTerm = SmtUtils.rational2Term(script, Rational.ZERO, divisorVar.getSort());
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

	private static boolean isEqOrDistinct(final RelationSymbol relSym) {
		return (relSym.equals(RelationSymbol.EQ)) || (relSym.equals(RelationSymbol.DISTINCT));
	}

	private static boolean isBvAndCantBeSolved(final Rational coeffOfSubject, final Monomial monomialOfSubject) {
		return SmtSortUtils.isBitvecSort(monomialOfSubject.getSort()) && (!monomialOfSubject.isLinear()
				|| !(coeffOfSubject.equals(Rational.ONE) || isBvMinusOne(coeffOfSubject, monomialOfSubject.getSort())));
	}

	private static boolean isBvMinusOne(final Rational number, final Sort bvSort) {
		final int vecSize = Integer.parseInt(bvSort.getIndices()[0]);
		final BigInteger minusOne = BigInteger.valueOf(2).pow(vecSize).subtract(BigInteger.ONE);
		final Rational rationalMinusOne = Rational.valueOf(minusOne, BigInteger.ONE);
		return number.equals(rationalMinusOne);
	}

	private static boolean isNegative(final Rational coeffOfSubject, final Sort sort) {
		return coeffOfSubject.isNegative() || (SmtSortUtils.isBitvecSort(sort) && isBvMinusOne(coeffOfSubject, sort));
	}

	private static LBool assumptionImpliesEquivalence(final Script script, final Term originalTerm,
			final Term relationToTerm, final Map<AssumptionForSolvability, Term> additionalAssumptions) {
		final Term konJ = SmtUtils.and(script, additionalAssumptions.values());
		final Term impli1 = SmtUtils.implies(script, konJ, relationToTerm);
		final Term impli2 = SmtUtils.implies(script, konJ, originalTerm);
		return SmtUtils.checkEquivalence(impli1, impli2, script);
	}

}
