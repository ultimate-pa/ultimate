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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;

/**
 * Represents an term of the form ψ ▷ φ, where ψ and φ are affine terms and ▷ is a binary relation symbol. Allows to
 * return this relation as an SMT term in the following two forms:
 * <ul>
 * <li>positive normal form
 * <li>the form where a specific variable is on the left hand side and all other summands are moved to the right hand
 * side.
 * </ul>
 *
 * @author Matthias Heizmann
 */
public class AffineRelation {
	private final Term mOriginalTerm;
	private final RelationSymbol mRelationSymbol;
	private final TrivialityStatus mTrivialityStatus;
	/**
	 * Affine term ψ such that the relation ψ ▷ 0 is equivalent to the mOriginalTerm.
	 *
	 */
	private final AffineTerm mAffineTerm;

	public enum TransformInequality {
		NO_TRANFORMATION, STRICT2NONSTRICT, NONSTRICT2STRICT
	}

	public enum TrivialityStatus {
		EQUIVALENT_TO_TRUE, EQUIVALENT_TO_FALSE, NONTRIVIAL
	}

	/**
	 * Create {@link AffineRelation} from {@link AffineTerm} and {@link RelationSymbol}.
	 *
	 * Resulting relation is then <code><term> <symbol> 0</code>.
	 */
	public AffineRelation(final Script script, final AffineTerm term, final RelationSymbol relationSymbol) {
		mAffineTerm = Objects.requireNonNull(term);
		mRelationSymbol = relationSymbol;
		mTrivialityStatus = computeTrivialityStatus(mAffineTerm, mRelationSymbol);
		if (VMUtils.areAssertionsEnabled()) {
			mOriginalTerm = term.toTerm(script);
		} else {
			mOriginalTerm = null;
		}
	}

	/**
	 * Transform {@link Term} to {@link AffineRelation} without transforming any equalities (i.e., by keeping the
	 * natural relation of the term).
	 *
	 * @param term
	 * @throws NotAffineException
	 */
	public AffineRelation(final Script script, final Term term) throws NotAffineException {
		this(script, term, TransformInequality.NO_TRANFORMATION);
	}

	/**
	 * Transform Term into AffineRelation.
	 *
	 * @param term
	 *            Term to which the resulting AffineRelation is equivalent.
	 * @param transformInequality
	 *            transform strict inequalities to non-strict inequalities and vice versa
	 * @throws NotAffineException
	 *             Thrown if Term is not affine.
	 */
	public AffineRelation(final Script script, final Term term, final TransformInequality transformInequality)
			throws NotAffineException {
		mOriginalTerm = term;
		BinaryNumericRelation bnr = null;
		try {
			bnr = new BinaryNumericRelation(term);
		} catch (final NoRelationOfThisKindException e) {
			throw new NotAffineException("Relation is not affine");
		}

		final Term lhs = bnr.getLhs();
		final Term rhs = bnr.getRhs();
		final AffineTerm affineLhs = (AffineTerm) new AffineTermTransformer(script).transform(lhs);
		final AffineTerm affineRhs = (AffineTerm) new AffineTermTransformer(script).transform(rhs);
		if (affineLhs.isErrorTerm() || affineRhs.isErrorTerm()) {
			throw new NotAffineException("Relation is not affine");
		}
		final AffineTerm difference = new AffineTerm(affineLhs, new AffineTerm(affineRhs, Rational.MONE));
		if (transformInequality != TransformInequality.NO_TRANFORMATION
				&& SmtSortUtils.isIntSort(difference.getSort())) {
			if (transformInequality == TransformInequality.STRICT2NONSTRICT) {
				switch (bnr.getRelationSymbol()) {
				case DISTINCT:
				case EQ:
				case GEQ:
				case LEQ:
					// relation symbol is not strict anyway
					mAffineTerm = difference;
					mRelationSymbol = bnr.getRelationSymbol();
					break;
				case LESS:
					// increment affine term by one
					mRelationSymbol = RelationSymbol.LEQ;
					mAffineTerm = new AffineTerm(difference, new AffineTerm(difference.getSort(), Rational.ONE));
					break;
				case GREATER:
					// decrement affine term by one
					mRelationSymbol = RelationSymbol.GEQ;
					mAffineTerm = new AffineTerm(difference, new AffineTerm(difference.getSort(), Rational.MONE));

					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else if (transformInequality == TransformInequality.NONSTRICT2STRICT) {
				switch (bnr.getRelationSymbol()) {
				case DISTINCT:
				case EQ:
				case LESS:
				case GREATER:
					// relation symbol is strict anyway
					mAffineTerm = difference;
					mRelationSymbol = bnr.getRelationSymbol();
					break;
				case GEQ:
					// increment affine term by one
					mRelationSymbol = RelationSymbol.GREATER;
					mAffineTerm = new AffineTerm(difference, new AffineTerm(difference.getSort(), Rational.ONE));
					break;
				case LEQ:
					// decrement affine term by one
					mRelationSymbol = RelationSymbol.LESS;
					mAffineTerm = new AffineTerm(difference, new AffineTerm(difference.getSort(), Rational.MONE));
					break;
				default:
					throw new AssertionError("unknown symbol");
				}
			} else {
				throw new AssertionError("unknown case");
			}
		} else {
			mAffineTerm = difference;
			mRelationSymbol = bnr.getRelationSymbol();
		}
		mTrivialityStatus = computeTrivialityStatus(mAffineTerm, mRelationSymbol);
	}

	private static TrivialityStatus computeTrivialityStatus(final AffineTerm term, final RelationSymbol symbol) {
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

	private static TrivialityStatus computeTrivialityStatus(final AffineTerm term, final Predicate<Integer> pred) {
		if (pred.test(term.getConstant().signum())) {
			return TrivialityStatus.EQUIVALENT_TO_TRUE;
		}
		return TrivialityStatus.EQUIVALENT_TO_FALSE;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	/**
	 * Return if term is variable (possibly with coefficient 0) in this affine relation.
	 */
	public boolean isVariable(final Term term) {
		return mAffineTerm.getVariable2Coefficient().containsKey(term);
	}

	/**
	 * Returns a term representation of this AffineRelation where each summand occurs only positive and the greater-than
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
			for (final Entry<Term, Rational> entry : mAffineTerm.getVariable2Coefficient().entrySet()) {
				if (entry.getValue().isNegative()) {
					rhsSummands.add(product(script, entry.getValue().abs(), entry.getKey()));
				} else {
					lhsSummands.add(product(script, entry.getValue(), entry.getKey()));
				}
			}
			if (mAffineTerm.getConstant() != Rational.ZERO) {
				if (mAffineTerm.getConstant().isNegative()) {
					rhsSummands.add(
							SmtUtils.rational2Term(script, mAffineTerm.getConstant().abs(), mAffineTerm.getSort()));
				} else {
					lhsSummands.add(SmtUtils.rational2Term(script, mAffineTerm.getConstant(), mAffineTerm.getSort()));
				}
			}
			final Term lhsTerm =
					SmtUtils.sum(script, mAffineTerm.getSort(), lhsSummands.toArray(new Term[lhsSummands.size()]));
			final Term rhsTerm =
					SmtUtils.sum(script, mAffineTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));
			final Term result = BinaryRelation.constructLessNormalForm(script, mRelationSymbol, lhsTerm, rhsTerm);
			assert isEquivalent(script, mOriginalTerm,
					result) != LBool.SAT : "transformation to positive normal form unsound";
			return result;
		}
	}

	/**
	 * Returns a term representation of this AffineRelation where the variable var (note that in our AffineTerms the
	 * variables may be SMT terms like e.g., a select term) is on the left hand side with coeffcient one. Throw a
	 * NotAffineException if no such representation is possible (e.g, if the variable does not occur in the term, or the
	 * variable is x, its sort is Int and the term is 2x=1.)
	 */
	public ApplicationTerm onLeftHandSideOnly(final Script script, final Term var) throws NotAffineException {
		assert mAffineTerm.getVariable2Coefficient().containsKey(var);
		final Rational termsCoeff = mAffineTerm.getVariable2Coefficient().get(var);
		if (termsCoeff.equals(Rational.ZERO)) {
			throw new NotAffineException("No affine representation " + "where desired variable is on left hand side");
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
					throw new NotAffineException(
							"No affine representation " + "where desired variable is on left hand side");
				}
			}
		}
		{
			if (!mAffineTerm.getSort().isNumericSort() && !termsCoeff.abs().equals(Rational.ONE)) {
				// for bitvectors we may only divide by 1 or -1
				throw new NotAffineException(
						"No affine representation " + "where desired variable is on left hand side");
			}
			final Rational newConstant = mAffineTerm.getConstant().div(termsCoeff);
			if (newConstant.isIntegral() && newConstant.isRational()
					|| SmtSortUtils.isRealSort(mAffineTerm.getSort())) {
				if (!newConstant.equals(Rational.ZERO)) {
					final Rational negated = newConstant.negate();
					rhsSummands.add(SmtUtils.rational2Term(script, negated, mAffineTerm.getSort()));
				}
			} else {
				throw new NotAffineException(
						"No affine representation " + "where desired variable is on left hand side");
			}
		}
		final Term rhsTerm =
				SmtUtils.sum(script, mAffineTerm.getSort(), rhsSummands.toArray(new Term[rhsSummands.size()]));

		// if coefficient is negative we have to use the "swapped"
		// RelationSymbol
		final boolean useRelationSymbolForSwappedTerms = termsCoeff.isNegative();
		final RelationSymbol relSymb =
				useRelationSymbolForSwappedTerms ? BinaryRelation.swapParameters(mRelationSymbol) : mRelationSymbol;
		final ApplicationTerm result = (ApplicationTerm) script.term(relSymb.toString(), var, rhsTerm);
		assert isEquivalent(script, mOriginalTerm, result) != LBool.SAT : "transformation to AffineRelation unsound";
		return result;
	}

	private static LBool isEquivalent(final Script script, final Term term1, final Term term2) {
		Term comp = script.term("=", term1, term2);
		comp = script.term("not", comp);
		final LBool sat = Util.checkSat(script, comp);
		return sat;
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

	public AffineTerm getAffineTerm() {
		return mAffineTerm;
	}

}
