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

import java.math.BigInteger;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * {@link IPolynomialRelation} implementation for bitvector inequalities. Keeps the left-hand side ({@link #mLhs}) and
 * right-hand side ({@link #mRhs}) as two separate polynomial terms, never combined via subtraction - reducing to a
 * single term compared against zero (the way {@link PolynomialRelation} does it) is unsound for bitvector
 * inequalities under two's-complement wraparound.
 * <p>
 * TODO: this class - and {@link PolyPoNe}'s handling of it, scoped so far to the "bare variable vs. bare constant"
 * shape (see {@link #isBareVariableVsBareConstant()}) - is not yet reachable from {@link IPolynomialRelation#of}
 * (those factory methods still always build a {@link PolynomialRelation} and still return {@code null}
 * for bitvector inequalities, exactly like before this class existed), so nothing currently depends on any of the
 * bodies below - they are safe to fill in incrementally.
 * <p>
 * TODO: {@code equals}/{@code hashCode}/{@code toString} are deliberately not overridden yet - what should count as
 * "equal" here (e.g. before vs. after canonicalization) needs to be decided together with the canonicalization
 * logic in the constructor, not assumed here.
 *
 * @author TODO add your name(s) here
 */
public class BitvectorInequalityRelation implements IPolynomialRelation {

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
	private BitvectorInequalityRelation(final RelationSymbol relationSymbol, final AbstractGeneralizedAffineTerm<?> lhs,
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
	 * Constructs a canonicalized {@link BitvectorInequalityRelation} for a bitvector inequality {@code term}, or
	 * {@code null} if {@code term} is not a binary relation, isn't a bitvector inequality (e.g. an equality, or an
	 * Int/Real relation - this factory is not for those; equalities stay on {@link PolynomialRelation},
	 * which is already sound for bitvector equality), or one of its sides could not be converted to a polynomial
	 * term. Null-safe on purpose - callers like {@link PolyPoNe} need to safely "try this, and if it doesn't apply,
	 * move on to something else" for an arbitrary atom, rather than assert a precondition only some callers could
	 * guarantee.
	 */
	public static BitvectorInequalityRelation of(final Script script, final Term term) {
		final BinaryNumericRelation bnr = BinaryNumericRelation.convert(term);
		if (bnr == null || !isBitvectorInequality(bnr.getRelationSymbol(), bnr.getLhs().getSort())) {
			return null; // not a bv inequality, not our job
		}
		final RelationSymbol relationSymbol = bnr.getRelationSymbol();
		final AbstractGeneralizedAffineTerm<?> polyLhs = transformToPolynomialTerm(script, bnr.getLhs());
		final AbstractGeneralizedAffineTerm<?> polyRhs = transformToPolynomialTerm(script, bnr.getRhs());
		if (polyLhs.isErrorTerm() || polyRhs.isErrorTerm()) {
			return null;
		}
		return new BitvectorInequalityRelation(relationSymbol, polyLhs, polyRhs);
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

	/**
	 * @return true iff exactly one side of this relation is a bare variable (coefficient 1, no offset) and the
	 *         other side is a bare constant - the only shape {@link PolyPoNe} currently knows how to compare cheaply
	 *         (see {@code PolyPoNe.mBvInequalityRels}). Anything else (both sides variables, either side compound like
	 *         {@code x - y}) is deliberately not handled yet.
	 */
	boolean isBareVariableVsBareConstant() {
		return (isBareVariable(mLhs) && mRhs.isConstant()) || (isBareVariable(mRhs) && mLhs.isConstant());
	}

	/**
	 * Only meaningful if {@link #isBareVariableVsBareConstant()} is true. True iff the bare variable is on the left
	 * (relation shape "var &#9657; const", an upper bound), false iff it's on the right ("const &#9657; var", a
	 * lower bound).
	 */
	boolean isVariableOnLhs() {
		return isBareVariable(mLhs);
	}

	/**
	 * Only meaningful if {@link #isBareVariableVsBareConstant()} is true.
	 */
	Term getBareVariableTerm(final Script script) {
		final AbstractGeneralizedAffineTerm<?> variableSide = isVariableOnLhs() ? mLhs : mRhs;
		return variableSide.getAbstractVariableAsTerm2Coefficient(script).keySet().iterator().next();
	}

	/**
	 * Only meaningful if {@link #isBareVariableVsBareConstant()} is true.
	 */
	BitvectorConstant getBareConstant() {
		final AbstractGeneralizedAffineTerm<?> constantSide = isVariableOnLhs() ? mRhs : mLhs;
		return BitvectorUtils.constructBitvectorConstant(constantSide.getConstant().numerator(),
				constantSide.getSort());
	}

	/**
	 * Only meaningful if {@link #isBareVariableVsBareConstant()} is true.
	 */
	Term getBareConstantTerm(final Script script) {
		final AbstractGeneralizedAffineTerm<?> constantSide = isVariableOnLhs() ? mRhs : mLhs;
		return constantSide.toTerm(script);
	}

	/**
	 * Combines the {@link #isBareVariableVsBareConstant()} check with extracting both sides in one call, instead of
	 * making callers do the check and then separately call {@link #getBareVariableTerm(Script)} and
	 * {@link #getBareConstantTerm(Script)} (each of which re-derives the orientation internally). Returns
	 * {@code null} if the shape doesn't apply.
	 */
	BareVariableAndConstant asBareVariableVsBareConstant(final Script script) {
		if (!isBareVariableVsBareConstant()) {
			return null;
		}
		return new BareVariableAndConstant(getBareVariableTerm(script), getBareConstantTerm(script));
	}

	/** Holds both sides of a {@link #isBareVariableVsBareConstant()} relation together - see {@link #asBareVariableVsBareConstant(Script)}. */
	static final class BareVariableAndConstant {
		private final Term mVariable;
		private final Term mConstantTerm;

		private BareVariableAndConstant(final Term variable, final Term constantTerm) {
			mVariable = variable;
			mConstantTerm = constantTerm;
		}

		Term getVariable() {
			return mVariable;
		}

		Term getConstantTerm() {
			return mConstantTerm;
		}
	}

	private static boolean isBareVariable(final AbstractGeneralizedAffineTerm<?> t) {
		return !t.isConstant() && t.getConstant().equals(Rational.ZERO) && t.getAbstractVariable2Coefficient().size() == 1
				&& t.getAbstractVariable2Coefficient().values().iterator().next().equals(Rational.ONE);
	}

	@Override
	public AbstractGeneralizedAffineTerm<?> getPolynomialTerm() {
		// There is no single polynomial term for a two-sided relation - see getLhs()/getRhs() instead. This method
		// only exists on the interface because some existing callers (ExplicitLhsPolynomialRelation,
		// PolyPoNeWithContext) call it on values statically typed as PolynomialRelation; those callers currently
		// only ever receive a SingleTermPolynomialRelation in practice, since this class isn't reachable via
		// PolynomialRelation.of yet.
		throw new UnsupportedOperationException(
				"BitvectorInequalityRelation has no single polynomial term - see getLhs()/getRhs() instead");
	}

	/**
	 * First tries {@link #tryCollapseAtSortBoundary(Script)} - a relation like {@code x <u 0} is always false, or
	 * {@code x <=u 0} is really just {@code x = 0}, purely because of where the constant sits relative to the
	 * sort's min/max, regardless of what the variable actually is. Falls back to the ordinary term construction
	 * when that doesn't apply (which is most of the time).
	 */
	@Override
	public Term toTerm(final Script script) {
		final Term collapsed = tryCollapseAtSortBoundary(script);
		if (collapsed != null) {
			return collapsed;
		}
		return mRelationSymbol.constructTerm(script, mLhs.toTerm(script), mRhs.toTerm(script));
	}

	/**
	 * Detects relations that are always true, always false, or reducible to an equality, purely because the
	 * constant sits exactly at the sort's unsigned/signed minimum or maximum - independent of the variable's
	 * actual value. Returns {@code null} if {@link #isBareVariableVsBareConstant()} is false, or if the constant
	 * doesn't sit at a boundary (the common case - most relations don't collapse at all).
	 * <p>
	 * The 6 boundary patterns (shown unsigned; the signed symbols follow the same shape against the signed
	 * min/max instead):
	 * <ul>
	 * <li>{@code x <u MIN} -&gt; {@code false} (nothing is strictly below the minimum)
	 * <li>{@code x <=u MIN} -&gt; {@code x = MIN} (only the minimum itself satisfies "at most the minimum")
	 * <li>{@code x <=u MAX} -&gt; {@code true} (every value satisfies "at most the maximum")
	 * <li>{@code MIN <=u x} -&gt; {@code true} (every value satisfies "at least the minimum")
	 * <li>{@code MAX <u x} -&gt; {@code false} (nothing is strictly above the maximum)
	 * <li>{@code MAX <=u x} -&gt; {@code x = MAX} (only the maximum itself satisfies "at least the maximum")
	 * </ul>
	 * ({@code MIN <u x} and {@code x <u MAX} are deliberately not in this list - each only excludes exactly one
	 * value, so they're genuine constraints, not a collapse.)
	 */
	Term tryCollapseAtSortBoundary(final Script script) {
		if (!isBareVariableVsBareConstant()) {
			return null; // no cheap shape to check
		}
		final boolean unsigned = mRelationSymbol == RelationSymbol.BVULT || mRelationSymbol == RelationSymbol.BVULE;
		final boolean strict = mRelationSymbol == RelationSymbol.BVULT || mRelationSymbol == RelationSymbol.BVSLT;
		final Sort sort = mLhs.getSort();
		final BitvectorConstant constant = getBareConstant();
		final BitvectorConstant min = sortMin(sort, unsigned);
		final BitvectorConstant max = sortMax(sort, unsigned);
		final boolean variableIsUpperBounded = isVariableOnLhs();
		final boolean constantIsMin = constant.equals(min);
		final boolean constantIsMax = constant.equals(max);

		if (variableIsUpperBounded) { // shape "x <> const"
			if (constantIsMin) {
				return strict ? script.term("false") : buildBoundaryEquality(script);
			}
			if (constantIsMax && !strict) {
				return script.term("true");
			}
		} else { // shape "const <> x"
			if (constantIsMax) {
				return strict ? script.term("false") : buildBoundaryEquality(script);
			}
			if (constantIsMin && !strict) {
				return script.term("true");
			}
		}
		return null; // no boundary hit, common case
	}

	private Term buildBoundaryEquality(final Script script) {
		return RelationSymbol.EQ.constructTerm(script, getBareVariableTerm(script), getBareConstantTerm(script));
	}

	/** The sort's unsigned minimum (0), or signed minimum, depending on {@code unsigned}. */
	static BitvectorConstant sortMin(final Sort sort, final boolean unsigned) {
		final int width = SmtSortUtils.getBitvectorLength(sort);
		return unsigned ? BitvectorUtils.constructBitvectorConstant(BigInteger.ZERO, sort)
				: BitvectorUtils.constructBitvectorConstant(BigInteger.valueOf(2).pow(width - 1), sort);
	}

	/** The sort's unsigned maximum, or signed maximum, depending on {@code unsigned}. */
	static BitvectorConstant sortMax(final Sort sort, final boolean unsigned) {
		final int width = SmtSortUtils.getBitvectorLength(sort);
		return unsigned ? BitvectorConstant.maxValue(width)
				: BitvectorUtils.constructBitvectorConstant(BigInteger.valueOf(2).pow(width - 1).subtract(BigInteger.ONE),
						sort);
	}

	/**
	 * Only handles the case where {@code subject} is already alone on one side (the same "bare variable vs. bare
	 * constant" shape {@link PolyPoNe} knows how to compare, see {@link #isBareVariableVsBareConstant()}) - there is
	 * nothing to move/compute in that case, the answer is just the already-stored fields read back out. Returns
	 * {@code null} for anything else (a compound side, or solving for a variable that doesn't occur bare here) -
	 * genuinely solving for a subject buried in a bitvector expression would mean moving terms across the relation,
	 * which is exactly the operation that's unsafe for bitvectors under wraparound, and isn't attempted here.
	 */
	@Override
	public SolvedBinaryRelation solveForSubject(final Script script, final Term subject) {
		if (!isBareVariableVsBareConstant() || !subject.equals(getBareVariableTerm(script))) {
			return null; // wrong shape or wrong variable
		}
		// variable on the right: mirror the symbol
		final RelationSymbol symbol = isVariableOnLhs() ? mRelationSymbol : mRelationSymbol.swapParameters();
		return new SolvedBinaryRelation(subject, getBareConstantTerm(script), symbol);
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
	public BitvectorInequalityRelation negate() {
		return new BitvectorInequalityRelation(mRelationSymbol.negate(), mLhs, mRhs);
	}

	/**
	 * Not supported: multiplying both sides is not equivalent under bitvector wraparound. Example, signed 8 bit:
	 * {@code 0 <s -128} is false, but {@code -(-128) <s -0}, i.e. {@code -128 <s 0}, is true. See
	 * {@link #constructAlternativeRepresentation()} for the sound transformation.
	 */
	@Override
	public IPolynomialRelation mul(final Script script, final Rational r) {
		throw new UnsupportedOperationException(
				"mul is unsound for bitvector inequalities, use constructAlternativeRepresentation");
	}

	/**
	 * Returns the alternative representation of this relation: {@code lhs op rhs} becomes
	 * {@code (-rhs-1) op (-lhs-1)}, same symbol, sides swapped. The map {@code v -> -v-1} (the bitwise complement)
	 * reverses the order of all values, signed and unsigned, without an edge case, so the result is logically
	 * equivalent. Plain negation {@code v -> -v} is not: it fails at 0 (unsigned) and at the most negative value
	 * (signed).
	 */
	public BitvectorInequalityRelation constructAlternativeRepresentation() {
		return new BitvectorInequalityRelation(mRelationSymbol, complement(mRhs), complement(mLhs));
	}

	private static AbstractGeneralizedAffineTerm<?> complement(final AbstractGeneralizedAffineTerm<?> term) {
		final AbstractGeneralizedAffineTerm<?> negated =
				(AbstractGeneralizedAffineTerm<?>) PolynomialTermOperations.mul(term, Rational.MONE);
		return negated.add(Rational.MONE);
	}

	/**
	 * This class is specifically for inequalities (bvult/bvule/bvslt/bvsle after canonicalization) - equality
	 * already stays on {@link PolynomialRelation}, since equality IS safe to reduce to "one term vs zero"
	 * even for bitvectors. So there is never a simple equality to report here.
	 */
	@Override
	public SolvedBinaryRelation isSimpleEquality(final Script script) {
		return null;
	}

	@Override
	public BitvectorInequalityRelation tryToConvertToEquivalentNonStrictRelation() {
		// TODO: SingleTermPolynomialRelation's version is Int-sort-specific and uses an offset that
		// RelationSymbol.getOffsetForStrictToNonstrictTransformation() explicitly refuses to compute for
		// bitvectors. A bitvector version needs genuinely different, width-aware logic, not a shared implementation.
		throw new UnsupportedOperationException("TODO: not yet implemented");
	}

}
