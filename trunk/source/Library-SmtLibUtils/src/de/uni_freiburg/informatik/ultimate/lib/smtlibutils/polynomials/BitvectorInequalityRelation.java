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
 * {@link IPolynomialRelation} implementation for bitvector inequalities, i.e. {@code bvult}, {@code bvule},
 * {@code bvslt}, {@code bvsle} and their "greater" counterparts.
 * <p>
 * <b>Why a separate class.</b> {@link PolynomialRelation} brings a relation {@code lhs op rhs} into the form
 * {@code lhs - rhs op 0}. That is sound for Int/Real inequalities and for equalities of every sort, but not for
 * bitvector inequalities, because the subtraction wraps around modulo 2^n: {@code x <=u 5} holds for
 * {@code x = 0..5}, while {@code x - 5 <=u 0} only holds for {@code x = 5}. This class therefore keeps the left-hand
 * side ({@link #mLhs}) and the right-hand side ({@link #mRhs}) as two separate polynomial terms and never combines
 * them. Equalities and disequalities of bitvectors are not handled here, they stay on {@link PolynomialRelation}.
 * <p>
 * <b>Canonical form.</b> The constructor mirrors the four "greater" symbols to their "less" counterpart and swaps
 * the sides, so only BVULT, BVULE, BVSLT and BVSLE occur. For example, {@code (bvuge x 5)} is stored as
 * {@code 5 bvule x}. {@link #negate()} stays inside this form because it goes through the same constructor.
 * <p>
 * <b>Shapes.</b> What can be done with a relation depends on which sides are constants:
 * <ul>
 * <li><i>bare variable vs. bare constant</i> ({@code x <=u 5}, {@code 5 <u x}, see
 * {@link #isBareVariableVsBareConstant()}): a simple bound on one variable. Only for this shape can a relation
 * collapse at the sort boundary (see {@link #toTerm(Script)}), be solved for its variable
 * ({@link #solveForSubject(Script, Term)}), and be checked by {@link PolyPoNe} against known equalities and
 * disequalities {@code x != c} of that variable.
 * <li><i>polynomial vs. constant</i> ({@code x + y <=u 5}, {@code (bvnot x) <=u 100}, see
 * {@link #isPolynomialVsConstant()}): exactly one side is a constant, the other side is any polynomial.
 * {@link PolyPoNe} treats that polynomial as one unknown value and compares such relations only by their
 * constants.
 * <li><i>anything else</i> ({@code x <=u y}): there is no useful way to compare these, {@link PolyPoNe} keeps them
 * as they are.
 * </ul>
 * <p>
 * <b>Alternative representation.</b> A fact about an expression {@code e} can also be written as a fact about its
 * bitwise complement {@code -e-1}. For 8 bit, {@code x <=u 5} says the same as {@code 250 <=u bvnot(x)}.
 * {@link #constructAlternativeRepresentation()} computes this second spelling, and {@link PolyPoNe} uses it to compare
 * facts that are written differently. Plain negation {@code v -> -v} cannot be used for this: it reverses the order
 * of the values except at 0 (unsigned) and at the most negative value (signed), which is also why {@link #mul} is not
 * supported. The complement {@code v -> -v-1} reverses the order of all values without an exception.
 * <p>
 * <b>Usage.</b> The shared factory methods of {@link IPolynomialRelation} deliberately never build this class and
 * return {@code null} for bitvector inequalities; {@link PolyPoNe} calls {@link #of(Script, Term)} itself (see its
 * class documentation for how these relations are simplified). {@code equals} and {@code hashCode} are deliberately
 * not overridden: {@link PolyPoNe} relies on object identity.
 *
 * @author Roman Vintonyak
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
	 *         other side is a bare constant. Only for this shape does {@link PolyPoNe} look up known equalities and
	 *         fuse with "x != c", and only this shape can collapse at the sort boundary or be solved for the
	 *         variable.
	 */
	boolean isBareVariableVsBareConstant() {
		return (isBareVariable(mLhs) && mRhs.isConstant()) || (isBareVariable(mRhs) && mLhs.isConstant());
	}

	/**
	 * @return true iff exactly one side of this relation is a constant. The other side may be any expression, for
	 *         example {@code x + y}. {@link PolyPoNe} compares such relations by treating that expression as one
	 *         unknown value and comparing only the constants.
	 */
	boolean isPolynomialVsConstant() {
		return mLhs.isConstant() != mRhs.isConstant();
	}

	/**
	 * Only meaningful if {@link #isPolynomialVsConstant()} is true. True iff the non-constant side is on the left
	 * (relation shape "var &#9657; const", an upper bound), false iff it's on the right ("const &#9657; var", a
	 * lower bound).
	 */
	boolean isVariableOnLhs() {
		return !mLhs.isConstant();
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
	 * Combines the {@link #isPolynomialVsConstant()} check with extracting both sides in one call. The key is the
	 * bare variable if there is one, otherwise the whole non-constant expression (offset included), so two relations
	 * only share a key if their non-constant sides are the same expression. Returns {@code null} if the shape
	 * doesn't apply.
	 */
	PolynomialAndConstant asPolynomialVsConstant(final Script script) {
		if (!isPolynomialVsConstant()) {
			return null;
		}
		final AbstractGeneralizedAffineTerm<?> polynomialSide = isVariableOnLhs() ? mLhs : mRhs;
		final Term key =
				isBareVariableVsBareConstant() ? getBareVariableTerm(script) : polynomialSide.toTerm(script);
		return new PolynomialAndConstant(key, getBareConstantTerm(script));
	}

	/** Holds the key and the constant side of a {@link #isPolynomialVsConstant()} relation together. */
	static final class PolynomialAndConstant {
		private final Term mKey;
		private final Term mConstantTerm;

		private PolynomialAndConstant(final Term key, final Term constantTerm) {
			mKey = key;
			mConstantTerm = constantTerm;
		}

		Term getKey() {
			return mKey;
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
		// There is no single polynomial term for a two-sided relation - see getLhs()/getRhs() instead. Callers of
		// IPolynomialRelation.of never receive this class, because the shared factories return null for bitvector
		// inequalities. PolyPoNe checks for this class before it calls this method.
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
	 * Only handles the case where {@code subject} is already alone on one side (see
	 * {@link #isBareVariableVsBareConstant()}) - there is nothing to move or compute in that case, the answer is just
	 * the stored fields read back out. Returns {@code null} for anything else (a compound side, or another variable).
	 * Solving for a subject inside a bitvector expression would mean moving terms across the relation, which is
	 * unsound for bitvectors under wraparound, so it is not attempted.
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
		// same reason as for the other overload: moving terms across the relation is unsound under wraparound
		throw new UnsupportedOperationException("solving for a subject is not supported for bitvector inequalities");
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
		// The Int version (PolynomialRelation) adds an offset that RelationSymbol refuses to compute for bitvectors,
		// and a strict bound at the sort minimum or maximum has no non-strict form.
		throw new UnsupportedOperationException("not supported for bitvector inequalities");
	}

}
