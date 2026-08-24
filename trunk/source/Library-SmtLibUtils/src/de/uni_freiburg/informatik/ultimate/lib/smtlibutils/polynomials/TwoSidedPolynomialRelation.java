/*
 * Copyright (C) 2026 University of Freiburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * {@link PolynomialRelation} implementation for bitvector inequalities. Keeps the left-hand side ({@link #mLhs}) and
 * right-hand side ({@link #mRhs}) as two separate polynomial terms, never combined via subtraction - reducing to a
 * single term compared against zero (the way {@link SingleTermPolynomialRelation} does it) is unsound for bitvector
 * inequalities under two's-complement wraparound.
 * <p>
 * TODO: this class is currently a skeleton. It is not yet reachable from {@link PolynomialRelation#of} (those
 * factory methods still always build a {@link SingleTermPolynomialRelation} and still return {@code null} for
 * bitvector inequalities, exactly like before this class existed), so nothing currently depends on any of the
 * bodies below - they are safe to fill in incrementally.
 * <p>
 * TODO: {@code equals}/{@code hashCode}/{@code toString} are deliberately not overridden yet - what should count as
 * "equal" here (e.g. before vs. after canonicalization) needs to be decided together with the canonicalization
 * logic in the constructor, not assumed here.
 *
 * @author TODO add your name(s) here
 */
public class TwoSidedPolynomialRelation implements PolynomialRelation {

	private final RelationSymbol mRelationSymbol;
	private final AbstractGeneralizedAffineTerm<?> mLhs;
	private final AbstractGeneralizedAffineTerm<?> mRhs;

	/**
	 * The 4 "greater" relation symbols get mirrored to their "less" counterpart by the constructor (swapping lhs and
	 * rhs), exactly like {@link de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils#unfTerm} does for
	 * terms via its {@code mirrorGreaterOperator} helper. This keeps every instance in canonical form (only
	 * BVULT/BVULE/BVSLT/BVSLE ever end up in {@link #mRelationSymbol}) from construction onward, so later
	 * comparison/fusion logic only has to handle 4 shapes instead of 8.
	 */
	private TwoSidedPolynomialRelation(final RelationSymbol relationSymbol, final AbstractGeneralizedAffineTerm<?> lhs,
			final AbstractGeneralizedAffineTerm<?> rhs) {
		if (isGreaterSymbol(relationSymbol)) {
			mRelationSymbol = relationSymbol.swapParameters();
			mLhs = rhs;
			mRhs = lhs;
		} else {
			mRelationSymbol = relationSymbol;
			mLhs = lhs;
			mRhs = rhs;
		}
	}

	private static boolean isGreaterSymbol(final RelationSymbol relationSymbol) {
		switch (relationSymbol) {
		case BVUGT:
		case BVUGE:
		case BVSGT:
		case BVSGE:
			return true;
		default:
			return false;
		}
	}

	/**
	 * Constructs a canonicalized {@link TwoSidedPolynomialRelation} for a bitvector inequality {@code term}, or
	 * {@code null} if {@code term} is not a binary relation / one of its sides could not be converted to a
	 * polynomial term. Throws if {@code term}'s relation symbol is not one of the 8 bitvector inequality symbols -
	 * this factory is not for equalities (those stay on {@link SingleTermPolynomialRelation}, which is already sound
	 * for bitvector equality) or for Int/Real relations.
	 */
	public static TwoSidedPolynomialRelation of(final Script script, final Term term) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null) {
			return null;
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		if (!isBitvectorInequality(relationSymbol, bnr.getLhs().getSort())) {
			throw new AssertionError(
					"TwoSidedPolynomialRelation.of is only for bitvector inequalities, got " + relationSymbol);
		}
		final AbstractGeneralizedAffineTerm<?> polyLhs = transformToPolynomialTerm(script, bnr.getLhs());
		final AbstractGeneralizedAffineTerm<?> polyRhs = transformToPolynomialTerm(script, bnr.getRhs());
		if (polyLhs.isErrorTerm() || polyRhs.isErrorTerm()) {
			return null;
		}
		return new TwoSidedPolynomialRelation(relationSymbol, polyLhs, polyRhs);
	}

	private static boolean isBitvectorInequality(final RelationSymbol relationSymbol, final Sort sort) {
		return relationSymbol.isConvexInequality() && SmtSortUtils.isBitvecSort(sort);
	}

	private static AbstractGeneralizedAffineTerm<?> transformToPolynomialTerm(final Script script, final Term term) {
		return (AbstractGeneralizedAffineTerm<?>) PolynomialTermTransformer.convert(script, term);
	}

	@Override
	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public AbstractGeneralizedAffineTerm<?> getLhs() {
		return mLhs;
	}

	public AbstractGeneralizedAffineTerm<?> getRhs() {
		return mRhs;
	}

	@Override
	public AbstractGeneralizedAffineTerm<?> getPolynomialTerm() {
		// There is no single polynomial term for a two-sided relation - see getLhs()/getRhs() instead. This method
		// only exists on the interface because some existing callers (ExplicitLhsPolynomialRelation,
		// PolyPoNeWithContext) call it on values statically typed as PolynomialRelation; those callers currently
		// only ever receive a SingleTermPolynomialRelation in practice, since this class isn't reachable via
		// PolynomialRelation.of yet.
		throw new UnsupportedOperationException(
				"TwoSidedPolynomialRelation has no single polynomial term - see getLhs()/getRhs() instead");
	}

	/**
	 * Note: {@link SingleTermPolynomialRelation#toTerm} additionally collapses to {@code true}/{@code false} via its
	 * {@code TrivialityStatus}, but {@code computeTrivialityStatus} there currently returns {@code NONTRIVIAL}
	 * unconditionally for all 8 bitvector relation symbols - so there is nothing to collapse yet for this class
	 * either. Real bitvector min/max-based triviality detection is a follow-up, not part of this pass.
	 */
	@Override
	public Term toTerm(final Script script) {
		return mRelationSymbol.constructTerm(script, mLhs.toTerm(script), mRhs.toTerm(script));
	}

	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		// TODO: needs real design work - solving for a subject means moving terms across the relation, which is
		// exactly the operation that's unsafe for bitvectors under wraparound. Not a copy-paste of
		// SingleTermPolynomialRelation's version.
		throw new UnsupportedOperationException("TODO: not yet implemented");
	}

	@Override
	public MultiCaseSolvedBinaryRelation solveForSubject(final ManagedScript mgdScript, final Term subject,
			final MultiCaseSolvedBinaryRelation.Xnf xnf, final Set<TermVariable> bannedForDivCapture,
			final boolean allowDivModBasedSolution) {
		// TODO: same reasoning as the other solveForSubject overload above.
		throw new UnsupportedOperationException("TODO: not yet implemented");
	}

	@Override
	public boolean isAffine() {
		return mLhs.isAffine() && mRhs.isAffine();
	}

	@Override
	public boolean isVariable(final Term var) {
		return mLhs.isVariable(var) || mRhs.isVariable(var);
	}

	/**
	 * Relies on the constructor's canonicalization to re-mirror lhs/rhs if {@code mRelationSymbol.negate()} produces
	 * one of the 4 "greater" symbols again (e.g. negating BVULT gives BVUGE, which the constructor then swaps back
	 * to BVULE with lhs/rhs swapped), so the result stays in canonical form.
	 */
	@Override
	public TwoSidedPolynomialRelation negate() {
		return new TwoSidedPolynomialRelation(mRelationSymbol.negate(), mLhs, mRhs);
	}

	@Override
	public PolynomialRelation mul(final Script script, final Rational r) {
		// TODO: needs real design work - multiplying a bitvector relation by a constant involves bitvector
		// multiplication, which wraps too, so this needs the same careful treatment as solveForSubject above.
		throw new UnsupportedOperationException("TODO: not yet implemented");
	}

	/**
	 * This class is specifically for inequalities (bvult/bvule/bvslt/bvsle after canonicalization) - equality
	 * already stays on {@link SingleTermPolynomialRelation}, since equality IS safe to reduce to "one term vs zero"
	 * even for bitvectors. So there is never a simple equality to report here.
	 */
	@Override
	public SolvedBinaryRelation isSimpleEquality(final Script script) {
		return null;
	}

	@Override
	public TwoSidedPolynomialRelation tryToConvertToEquivalentNonStrictRelation() {
		// TODO: SingleTermPolynomialRelation's version is Int-sort-specific and uses an offset that
		// RelationSymbol.getOffsetForStrictToNonstrictTransformation() explicitly refuses to compute for
		// bitvectors. A bitvector version needs genuinely different, width-aware logic, not a shared implementation.
		throw new UnsupportedOperationException("TODO: not yet implemented");
	}

}
