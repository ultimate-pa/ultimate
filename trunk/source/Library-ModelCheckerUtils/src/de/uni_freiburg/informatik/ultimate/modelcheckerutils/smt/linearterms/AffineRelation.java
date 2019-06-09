/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.INonSolverScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are
 * {@link AffineTerm}s and ▷ is a binary relation symbol from the following
 * list.
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
 * @author Matthias Heizmann, Max Barth
 */
public class AffineRelation extends AbstractGeneralizedaAffineRelation {

	public AffineRelation(final Script script, final AffineTerm term, final RelationSymbol relationSymbol) {
		super(script, term, relationSymbol);
	}

//	public AffineRelation(final Script script, final Term term, final TransformInequality transformInequality) throws NotAffineException {
//		super(script, term, transformInequality);
//	}

//	public AffineRelation(final Script script, final Term term) throws NotAffineException {
//		super(script, term);
//	}



	public AffineRelation(final Script script, final TransformInequality transformInequality, final RelationSymbol relationSymbol,
			final AffineTerm affineLhs, final AffineTerm affineRhs, final Term term) {
		super(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
	}

	static AffineTerm transformToAffineTerm(final Script script, final Term term) {
		if (TEMPORARY_POLYNOMIAL_TERM_TEST) {
			final IPolynomialTerm polynomialTerm = (IPolynomialTerm) new PolynomialTermTransformer(script)
					.transform(term);
			final Term toTerm = polynomialTerm.toTerm(script);
			final LBool lbool = Util.checkSat(script, script.term("distinct", term, toTerm));
			if (lbool != LBool.UNSAT) {
				throw new AssertionError(
						"Input and output is not equivalent (" + lbool + "). Input: " + term + " Output: " + toTerm);
			}
		}
		return (AffineTerm) new AffineTermTransformer(script).transform(term);
	}

	@Override
	protected AffineTerm sum(final AffineTerm op1, final AffineTerm op2) {
		return AffineTerm.sum(op1, op2);
	}

	@Override
	protected AffineTerm mul(final AffineTerm op, final Rational r) {
		return AffineTerm.mul(op, r);
	}

	@Override
	protected AffineTerm constructConstant(final Sort s, final Rational r) {
		return AffineTerm.constructConstant(s, r);
	}

	public static AffineRelation convert(final Script script, final Term term) {
		return convert(script, term, TransformInequality.NO_TRANFORMATION);
	}

	public static AffineRelation convert(final Script script, final Term term, final TransformInequality transformInequality) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AffineTerm affineLhs = transformToAffineTerm(script, lhs);
		final AffineTerm affineRhs = transformToAffineTerm(script, rhs);
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		return new AffineRelation(script, transformInequality, relationSymbol, affineLhs, affineRhs, term);
	}

	/**
	 * Returns a term representation of this AffineRelation where the variable var
	 * (note that in our AffineTerms the variables may be SMT terms like e.g., a
	 * select term) is on the left hand side with coeffcient one. Throw a
	 * NotAffineException if no such representation is possible (e.g, if the
	 * variable does not occur in the term, or the variable is x, its sort is Int
	 * and the term is 2x=1.)
	 */
	public ApplicationTerm onLeftHandSideOnly(final Script script, final Term var) throws NotAffineException {
		assert mAffineTerm.getVariable2Coefficient().containsKey(var);
		final Rational termsCoeff = mAffineTerm.getVariable2Coefficient().get(var);
		if (termsCoeff.equals(Rational.ZERO)) {
			throw new NotAffineException(NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE);
		}
		final List<Term> rhsSummands = new ArrayList<>(mAffineTerm.getVariable2Coefficient().size());
		for (final Entry<Term, Rational> entry : mAffineTerm.getVariable2Coefficient().entrySet()) {
			if (var == entry.getKey()) {
				// do nothing
			} else {
				final Rational newCoeff = entry.getValue().div(termsCoeff);
				if (newCoeff.isIntegral() || SmtSortUtils.isRealSort(mAffineTerm.getSort())) {
					final Rational negated = newCoeff.negate();
					rhsSummands.add(product(script, negated, entry.getKey()));
				} else {
					throw new NotAffineException(NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE);
				}
			}
		}
		{
			if (!mAffineTerm.getSort().isNumericSort() && !termsCoeff.abs().equals(Rational.ONE)) {
				// for bitvectors we may only divide by 1 or -1
				throw new NotAffineException(NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE);
			}
			final Rational newConstant = mAffineTerm.getConstant().div(termsCoeff);
			if (newConstant.isIntegral() && newConstant.isRational()
					|| SmtSortUtils.isRealSort(mAffineTerm.getSort())) {
				if (!newConstant.equals(Rational.ZERO)) {
					final Rational negated = newConstant.negate();
					rhsSummands.add(SmtUtils.rational2Term(script, negated, mAffineTerm.getSort()));
				}
			} else {
				throw new NotAffineException(NO_AFFINE_REPRESENTATION_WHERE_DESIRED_VARIABLE_IS_ON_LEFT_HAND_SIDE);
			}
		}
		final Term rhsTerm = SmtUtils.sum(script, mAffineTerm.getSort(),
				rhsSummands.toArray(new Term[rhsSummands.size()]));

		// if coefficient is negative we have to use the "swapped"
		// RelationSymbol
		final boolean useRelationSymbolForSwappedTerms = termsCoeff.isNegative();
		final RelationSymbol relSymb = useRelationSymbolForSwappedTerms ? BinaryRelation.swapParameters(mRelationSymbol)
				: mRelationSymbol;
		final ApplicationTerm result = (ApplicationTerm) script.term(relSymb.toString(), var, rhsTerm);
		assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
				result) != LBool.SAT : "transformation to AffineRelation unsound";
		return result;
	}

	/**
	 * Optimization of onLeftHandSideOnly.
	 *
	 * mAffineTerm: a = 2 * b and var: b
	 *
	 * Result: b = (a div 2) AND ((a mod 2) = 0)
	 *
	 * If Optimization is not needed, returns the Pair(onLeftHandSideOnly(script,
	 * var), true)
	 *
	 */
	public Pair<ApplicationTerm, ApplicationTerm> onLeftHandSideOnlyWithIntegerDivision(final Script script,
			final Term var) throws NotAffineException {
		Term withOutModulo = null;
		final Term moduloConjunct = script.term("true");
		try {
			withOutModulo = onLeftHandSideOnly(script, var);
		} catch (final NotAffineException nae) {
			if (mAffineTerm.getSort().equals(SmtSortUtils.getIntSort(script))) {
				final Rational termsCoeff = mAffineTerm.getVariable2Coefficient().get(var);
				if (termsCoeff.equals(Rational.ZERO)) {
					throw nae;
				}
				final Term divisor = SmtUtils.rational2Term(script, termsCoeff, var.getSort());
				final List<Term> rhsSummands = new ArrayList<>(mAffineTerm.getVariable2Coefficient().size());
				for (final Entry<Term, Rational> entry : mAffineTerm.getVariable2Coefficient().entrySet()) {
					if (var != entry.getKey()) {
						final Term entryValueTerm = SmtUtils.rational2Term(script, entry.getValue().negate(),
								entry.getKey().getSort());
						final Term newCoeff = SmtUtils.mul(script, entry.getKey().getSort(), entry.getKey(),
								entryValueTerm);

						rhsSummands.add(newCoeff);

					}
				}

				final Term withOutConst = SmtUtils.sum(script, mAffineTerm.getSort(),
						rhsSummands.toArray(new Term[rhsSummands.size()]));

				final List<Term> constSummands = new ArrayList<>(mAffineTerm.getVariable2Coefficient().size());
				final Rational newConstant = mAffineTerm.getConstant().div(termsCoeff);
				if (newConstant.isIntegral() && newConstant.isRational()) {
					if (!newConstant.equals(Rational.ZERO)) {
						final Rational negated = newConstant.negate();
						constSummands.add(SmtUtils.rational2Term(script, negated, mAffineTerm.getSort()));
					}
				} else {

					throw nae;
				}

				final Term constSum = SmtUtils.sum(script, mAffineTerm.getSort(),
						constSummands.toArray(new Term[constSummands.size()]));

				Term modTerm = SmtUtils.mod(script, withOutConst, divisor);
				Term divTerm = SmtUtils.div(script, withOutConst, divisor);

				modTerm = SmtUtils.binaryEquality(script, modTerm, TermParseUtils.parseTerm(script, "0"));

				// x>=((b*y+c*z+d) div a) + 1
				// mRelationSymbol == RelationSymbol.LESS ||

				withOutModulo = SmtUtils.sum(script, mAffineTerm.getSort(), constSum, divTerm);

				// if coefficient is negative, use the "swapped" RelationSymbol
				final boolean useRelationSymbolForSwappedTerms = termsCoeff.isNegative();
				final RelationSymbol relSymb = useRelationSymbolForSwappedTerms
						? BinaryRelation.swapParameters(mRelationSymbol)
						: mRelationSymbol;
				Term conjTerm = script.term("false");

				if (relSymb == RelationSymbol.GEQ) {
					conjTerm = SmtUtils.sum(script, mAffineTerm.getSort(), constSum,
							TermParseUtils.parseTerm(script, "1"), divTerm);
					conjTerm = script.term(relSymb.toString(), var, conjTerm);

				} else if (relSymb == RelationSymbol.LEQ || relSymb == RelationSymbol.GREATER) {
					modTerm = script.term("true");
				} else if (relSymb == RelationSymbol.LESS) {
					// TODO

				}

				divTerm = script.term(relSymb.toString(), var, withOutModulo);
				// divTerm = SmtUtils.or(script, divTerm, conjTerm);
				modTerm = SmtUtils.or(script, modTerm, conjTerm);
				// check if result is unsound
				final Term soundResult = SmtUtils.and(script, modTerm, divTerm);
				assert script instanceof INonSolverScript || isEquivalent(script, mOriginalTerm,
						soundResult) != LBool.SAT : "transformation to AffineRelation unsound";
				return new Pair<>((ApplicationTerm) divTerm, (ApplicationTerm) modTerm);
			} else {
				throw nae;
			}
		}
		return new Pair<>((ApplicationTerm) withOutModulo, (ApplicationTerm) moduloConjunct);
	}

}
