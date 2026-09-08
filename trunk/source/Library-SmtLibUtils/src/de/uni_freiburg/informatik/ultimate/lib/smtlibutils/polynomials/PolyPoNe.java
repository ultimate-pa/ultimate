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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Internal data structure that we use to construct simplified conjunctions and disjunction. We distinguish three kinds
 * of parameters of the disjunction/conjunction.
 * <li>polynomial parameter: params that can be converted into a {@link PolynomialRelation}
 * <li>negative parameters: params that cannot be converted into a {@link PolynomialRelation} and are negated
 * <li>negative parameters: all other params.
 *
 * Based on a pairwise comparison of params, we decide whether a parameter is redundant and can be omitted or whether
 * the result for two parameters is already the absorbing element of the operation.
 *
 * For disjunctions we store negated versions of the {@link PolynomialRelation}s, apply the rules for conjunctions, and
 * negate all {@link PolynomialRelation} before computing the result.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolyPoNe {

	protected enum Check {
		REDUNDANT, INCONSISTENT, MAYBE_USEFUL
	}

	protected final Script mScript;
	protected final Junction mJunction;
	private final Set<Term> mPositive = new HashSet<>();
	private final Set<Term> mNegative = new HashSet<>();
	private final HashRelation<Map<?, Rational>, PolynomialRelation> mPolyRels = new HashRelation<>();
	/**
	 * Bitvector-inequality analogue of {@link #mPolyRels}, scoped to relations of the shape "bare variable vs. bare
	 * constant" (e.g. {@code x <=u 5}) - keyed directly on the variable {@link Term} since there is no single
	 * combined polynomial to key on the way {@link #mPolyRels} does. See {@link BitvectorInequalityRelation}.
	 */
	private final HashRelation<Term, BitvectorInequalityRelation> mBvInequalityRels = new HashRelation<>();
	/**
	 * {@link BitvectorInequalityRelation}s that are not "bare variable vs. bare constant" (both sides variables, or
	 * either side compound like {@code x - y}) - no cheap key available, so these are just kept as-is and never
	 * compared against anything.
	 */
	private final Set<BitvectorInequalityRelation> mCompoundBvInequalityRels = new HashSet<>();
	private boolean mInconsistent = false;

	PolyPoNe(final Script script, final Junction junction) {
		mScript = script;
		mJunction = junction;
	}

	public boolean isInconsistent() {
		return mInconsistent;
	}

	void add(final Collection<Term> params, final boolean negate) {
		for (final Term param : params) {
			// TODO 20201123 Matthias: For bitvectors distinct and equality are polynomial,
			// the other inequalities not, hence distinct and equality should also be added
			// as nonPoly. Add another data structure for binary relations
			PolynomialRelation polyPolyRel;
			if (negate) {
				polyPolyRel = PolynomialRelation.of(mScript, param, TransformInequality.NONSTRICT2STRICT);
			} else {
				polyPolyRel = PolynomialRelation.of(mScript, param, TransformInequality.STRICT2NONSTRICT);
			}
			if (polyPolyRel == null) {
				// INTERIM STEP: the shared factory above still never returns a BitvectorInequalityRelation (that
				// would affect ~15 other, unaudited callers of PolynomialRelation.of across the codebase) - so
				// PolyPoNe tries it here instead, only for itself, now that Phase B has made this class safe to
				// use. The "real" fix would be moving this into PolynomialRelation.of once those other callers are
				// checked too, and deleting this second attempt.
				polyPolyRel = BitvectorInequalityRelation.ofIfApplicable(mScript, param);
			}
			if (polyPolyRel != null) {
				final PolynomialRelation addedRel = negate ? polyPolyRel.negate() : polyPolyRel;
				final boolean isInconsistent = addPolyRel(mScript, addedRel, true);
				if (isInconsistent) {
					mInconsistent = true;
					return;
				}
			} else {
				final Term addedNonPolyRel = negate ? SmtUtils.not(mScript, param) : param;
				final boolean isInconsistent = addNonPolynomial(addedNonPolyRel);
				if (isInconsistent) {
					mInconsistent = true;
					return;
				}
			}
		}
	}

	Term and(final List<Term> params) {
		add(params, false);
		return and();
	}

	Term or(final List<Term> params) {
		add(params, true);
		return or();
	}

	protected final Check checkPolyRel(final Script script, final PolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Check res1 = compareToExistingRepresentations(newPolyRel, removeExpliedPolyRels);
		if (res1 == Check.INCONSISTENT || res1 == Check.REDUNDANT) {
			return res1;
		}
		assert res1 == null;
		final PolynomialRelation alternativeRepresentation = newPolyRel.mul(mScript, Rational.MONE);
		final Check res2 = compareToExistingRepresentations(alternativeRepresentation, removeExpliedPolyRels);
		if (res2 == Check.INCONSISTENT || res2 == Check.REDUNDANT) {
			return res2;
		}
		assert res2 == null;
		return Check.MAYBE_USEFUL;
	}

	private Check compareToExistingRepresentations(final PolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Set<PolynomialRelation> existingPolyRels =
				mPolyRels.getImage(newPolyRel.getPolynomialTerm().getAbstractVariable2Coefficient());
		final List<PolynomialRelation> existingThatExplyNew = new ArrayList<>();
		for (final PolynomialRelation existingPolyRel : existingPolyRels) {
			final ComparisonResult comp =
					AbstractGeneralizedAffineTerm.compareRepresentation(existingPolyRel, newPolyRel);
			if (comp != null) {
				switch (comp) {
				case IMPLIES:
				case EQUIVALENT:
					return Check.REDUNDANT;
				case EXPLIES:
					if (removeExpliedPolyRels) {
						existingThatExplyNew.add(existingPolyRel);
					}
					break;
				case INCONSISTENT:
					return Check.INCONSISTENT;
				default:
					throw new AssertionError("unknown value " + comp);
				}
			}
		}
		if (removeExpliedPolyRels) {
			// remove all existing relations that exply the new relation (i.e., all that are
			// implied by the new relation)
			for (final PolynomialRelation existing : existingThatExplyNew) {
				final boolean modified =
						mPolyRels.removePair(existing.getPolynomialTerm().getAbstractVariable2Coefficient(), existing);
				assert modified : "nothing removed";
			}
		}
		return null;
	}

	protected PolynomialRelation isFusibleWithExistingRelations(final Script script, final Junction junction,
			final PolynomialRelation newPolyRel) {
		final PolynomialRelation res1 = isFusibleWithExistingRepresentation(junction, newPolyRel);
		if (res1 != null) {
			return res1;
		}
		final PolynomialRelation alternativeRepresentation = newPolyRel.mul(mScript, Rational.MONE);
		final PolynomialRelation res2 = isFusibleWithExistingRepresentation(junction, alternativeRepresentation);
		if (res2 != null) {
			return res2;
		}
		return null;
	}

	private PolynomialRelation isFusibleWithExistingRepresentation(final Junction junction,
			final PolynomialRelation newPolyRel) {
		final Set<PolynomialRelation> existingPolyRels =
				mPolyRels.getImage(newPolyRel.getPolynomialTerm().getAbstractVariable2Coefficient());
		for (final PolynomialRelation existingPolyRel : existingPolyRels) {
			final boolean res =
					AbstractGeneralizedAffineTerm.areRepresentationsFusible(junction, existingPolyRel, newPolyRel);
			if (res) {
				return existingPolyRel;
			}
		}
		return null;
	}

	protected boolean addPolyRel(final Script script, final PolynomialRelation polyRel,
			final boolean removeExpliedPolyRels) {
		if (mInconsistent) {
			throw new AssertionError("must not add if already inconsistent");
		}
		if (polyRel instanceof BitvectorInequalityRelation) {
			// Never call getPolynomialTerm() on a BitvectorInequalityRelation - it has no single polynomial term
			// (see BitvectorInequalityRelation.getPolynomialTerm()'s javadoc). Handled entirely separately below,
			// scoped to the "bare variable vs. bare constant" shape - see mBvInequalityRels' javadoc.
			return addTwoSidedPolyRel((BitvectorInequalityRelation) polyRel);
		}

		final Check check = checkPolyRel(script, polyRel, removeExpliedPolyRels);
		if (check == Check.MAYBE_USEFUL) {
			if (polyRel.getRelationSymbol().isConvexInequality()) {
				final PolynomialRelation fusionPartner = isFusibleWithExistingRelations(mScript, Junction.AND, polyRel);
				if (fusionPartner != null) {
					mPolyRels.removePair(fusionPartner.getPolynomialTerm().getAbstractVariable2Coefficient(),
							fusionPartner);
					final PolynomialRelation fusion =
							PolynomialRelation.of(polyRel.getPolynomialTerm(), RelationSymbol.EQ);
					mPolyRels.addPair(fusion.getPolynomialTerm().getAbstractVariable2Coefficient(), fusion);
					return false;
				}
			}
			mPolyRels.addPair(polyRel.getPolynomialTerm().getAbstractVariable2Coefficient(), polyRel);
			return false;
		} else if (check == Check.REDUNDANT) {
			return false;
		} else if (check == Check.INCONSISTENT) {
			return true;
		} else {
			throw new AssertionError("unknown value " + check);
		}
	}

	/**
	 * Bitvector-inequality analogue of {@link #addPolyRel}, scoped to the "bare variable vs. bare constant" shape
	 * (see {@link BitvectorInequalityRelation#isBareVariableVsBareConstant()}). Relations outside that shape are
	 * stored in {@link #mCompoundBvInequalityRels} unconditionally - no comparison is attempted for them, matching the
	 * "skip rather than do an expensive scan" instruction from Heizmann's meeting notes (see
	 * bitvector-inequality-relation-idea memory).
	 */
	private boolean addTwoSidedPolyRel(final BitvectorInequalityRelation polyRel) {
		if (!polyRel.isBareVariableVsBareConstant()) {
			mCompoundBvInequalityRels.add(polyRel); // no cheap key, keep as-is
			return false;
		}
		final Term variable = polyRel.getBareVariableTerm(mScript);
		// peek into the equality bin first - a known value can make this whole relation redundant or inconsistent
		final BitvectorConstant knownValue = findKnownEqualityValue(polyRel);
		if (knownValue != null) {
			return !satisfiesBound(knownValue, polyRel); // satisfies -> redundant (false); violates -> inconsistent (true)
		}
		final List<BitvectorInequalityRelation> explied = new ArrayList<>();
		for (final BitvectorInequalityRelation existing : mBvInequalityRels.getImage(variable)) {
			final ComparisonResult comp = compareTwoSidedRepresentation(existing, polyRel);
			if (comp == null) {
				continue; // no verdict, e.g. different orientation
			}
			switch (comp) {
			case IMPLIES:
			case EQUIVALENT:
				return false; // polyRel redundant
			case EXPLIES:
				explied.add(existing); // existing redundant, drop later
				break;
			case INCONSISTENT:
				return true;
			default:
				throw new AssertionError("unknown value " + comp);
			}
		}
		for (final BitvectorInequalityRelation existing : explied) {
			mBvInequalityRels.removePair(variable, existing);
		}
		final BitvectorInequalityRelation fusionPartner = findFusibleTwoSidedRelation(variable, polyRel);
		if (fusionPartner != null) {
			// fuse into an equality, reuse the existing single-term insertion path
			mBvInequalityRels.removePair(variable, fusionPartner);
			final PolynomialRelation fusion = SingleTermPolynomialRelation.of(mScript, RelationSymbol.EQ, variable,
					polyRel.getBareConstantTerm(mScript));
			return addPolyRel(mScript, fusion, true);
		}
		mBvInequalityRels.addPair(variable, polyRel);
		return false;
	}

	/**
	 * Compares two {@link BitvectorInequalityRelation}s that are both "bare variable vs. bare constant" and share the
	 * same variable (same {@link HashRelation} bucket in {@link #mBvInequalityRels}). Handles mixed strictness (e.g.
	 * {@code x <=u 7} vs. {@code x <u 9}) by normalizing both to an "effective inclusive boundary" first - see
	 * {@link #effectiveInclusiveBoundary}. Returns {@code null} if the signedness differs, the variable is on
	 * different sides, or normalizing either side would underflow/overflow (no verdict attempted in this pass - see
	 * the "open question" note in the Phase B plan about the variable-vs-variable case).
	 */
	private static ComparisonResult compareTwoSidedRepresentation(final BitvectorInequalityRelation existing,
			final BitvectorInequalityRelation newRel) {
		final boolean existingUnsigned = isUnsigned(existing.getRelationSymbol());
		if (existingUnsigned != isUnsigned(newRel.getRelationSymbol())) {
			return null; // different signedness
		}
		if (existing.isVariableOnLhs() != newRel.isVariableOnLhs()) {
			return null; // different orientation
		}
		final BitvectorConstant existingBoundary = effectiveInclusiveBoundary(existing);
		final BitvectorConstant newBoundary = effectiveInclusiveBoundary(newRel);
		if (existingBoundary == null || newBoundary == null) {
			return null; // would underflow/overflow, decline rather than guess
		}
		if (existingBoundary.equals(newBoundary)) {
			return ComparisonResult.EQUIVALENT;
		}
		final boolean existingIsSmaller = existingUnsigned ? BitvectorConstant.bvult(existingBoundary, newBoundary)
				: BitvectorConstant.bvslt(existingBoundary, newBoundary);
		if (existing.isVariableOnLhs()) {
			// relation shape "var <>= const" (upper bound) - the smaller boundary is the tighter constraint.
			return existingIsSmaller ? ComparisonResult.IMPLIES : ComparisonResult.EXPLIES;
		} else {
			// relation shape "const <>= var" (lower bound) - the larger boundary is the tighter constraint.
			return existingIsSmaller ? ComparisonResult.EXPLIES : ComparisonResult.IMPLIES;
		}
	}

	private static boolean isUnsigned(final RelationSymbol symbol) {
		return symbol == RelationSymbol.BVULE || symbol == RelationSymbol.BVULT;
	}

	private static boolean isStrict(final RelationSymbol symbol) {
		return symbol == RelationSymbol.BVULT || symbol == RelationSymbol.BVSLT;
	}

	/**
	 * Converts a strict relation into its equivalent non-strict form (e.g. {@code x <u 9} behaves like
	 * {@code x <=u 8}), so relations with different strictness can be compared directly by just comparing this
	 * boundary value. Returns {@code null} if that conversion would underflow/overflow (the constant is already at
	 * the sort's min/max) - declined rather than risking a wrapped, wrong value. That case only arises for
	 * relations {@link BitvectorInequalityRelation#tryCollapseAtSortBoundary} would already reduce to true/false
	 * anyway.
	 */
	private static BitvectorConstant effectiveInclusiveBoundary(final BitvectorInequalityRelation rel) {
		final BitvectorConstant constant = rel.getBareConstant();
		if (!isStrict(rel.getRelationSymbol())) {
			return constant;
		}
		final boolean unsigned = isUnsigned(rel.getRelationSymbol());
		final Sort sort = rel.getLhs().getSort();
		final BitvectorConstant one = BitvectorUtils.constructBitvectorConstant(BigInteger.ONE, sort);
		if (rel.isVariableOnLhs()) {
			// "x < c" -> "x <= c-1"; underflow if c is already the minimum
			if (constant.equals(BitvectorInequalityRelation.sortMin(sort, unsigned))) {
				return null;
			}
			return BitvectorConstant.bvsub(constant, one);
		} else {
			// "c < x" -> "c+1 <= x"; overflow if c is already the maximum
			if (constant.equals(BitvectorInequalityRelation.sortMax(sort, unsigned))) {
				return null;
			}
			return BitvectorConstant.bvadd(constant, one);
		}
	}

	/**
	 * Looks up an existing equality (in {@link #mPolyRels}) about exactly the same bare variable as {@code polyRel},
	 * and returns the value it pins that variable to, or {@code null} if there is none. Deliberately narrow: only
	 * finds equalities whose variable side has the exact same shape as a bare variable (coefficient 1, no offset) -
	 * an equality where that variable's coefficient ended up negated (e.g. depending on which side it was
	 * originally written on) may be missed. Never wrong, just occasionally too conservative - same "skip rather
	 * than guess" pattern as elsewhere in this class.
	 */
	private BitvectorConstant findKnownEqualityValue(final BitvectorInequalityRelation polyRel) {
		final AbstractGeneralizedAffineTerm<?> variableSide =
				polyRel.isVariableOnLhs() ? polyRel.getLhs() : polyRel.getRhs();
		for (final PolynomialRelation existing : mPolyRels.getImage(variableSide.getAbstractVariable2Coefficient())) {
			if (existing.getRelationSymbol() == RelationSymbol.EQ) {
				// existing's ψ is "variable - value", so its constant is -value
				final Rational value = existing.getPolynomialTerm().getConstant().negate();
				return BitvectorUtils.constructBitvectorConstant(value.numerator(), variableSide.getSort());
			}
		}
		return null; // no known equality for this variable
	}

	/** Does the concrete value {@code value} satisfy {@code rel}'s bound? */
	private static boolean satisfiesBound(final BitvectorConstant value, final BitvectorInequalityRelation rel) {
		final BitvectorConstant constant = rel.getBareConstant();
		final boolean unsigned = isUnsigned(rel.getRelationSymbol());
		final boolean strict = isStrict(rel.getRelationSymbol());
		if (rel.isVariableOnLhs()) { // "value <> constant"
			if (strict) {
				return unsigned ? BitvectorConstant.bvult(value, constant) : BitvectorConstant.bvslt(value, constant);
			}
			return unsigned ? BitvectorConstant.bvule(value, constant) : BitvectorConstant.bvsle(value, constant);
		}
		// "constant <> value"
		if (strict) {
			return unsigned ? BitvectorConstant.bvult(constant, value) : BitvectorConstant.bvslt(constant, value);
		}
		return unsigned ? BitvectorConstant.bvule(constant, value) : BitvectorConstant.bvsle(constant, value);
	}

	/**
	 * Mirrors {@link AbstractGeneralizedAffineTerm#areRepresentationsFusible} for the two-sided bitvector case:
	 * fusion only applies to non-strict relations (BVULE/BVSLE - BVULT/BVSLT can't fuse into an equality the same
	 * way, see {@code areRepresentationsFusibleHelper}'s AND case), with opposite orientation (one upper bound, one
	 * lower bound on the same variable) and an equal constant, e.g. {@code x <=u 5 /\ x >=u 5 -> x = 5}.
	 */
	private BitvectorInequalityRelation findFusibleTwoSidedRelation(final Term variable,
			final BitvectorInequalityRelation polyRel) {
		if (polyRel.getRelationSymbol() != RelationSymbol.BVULE && polyRel.getRelationSymbol() != RelationSymbol.BVSLE) {
			return null; // strict relations don't fuse
		}
		for (final BitvectorInequalityRelation existing : mBvInequalityRels.getImage(variable)) {
			if (existing.getRelationSymbol() != polyRel.getRelationSymbol()) {
				continue;
			}
			if (existing.isVariableOnLhs() == polyRel.isVariableOnLhs()) {
				continue; // need opposite orientation (upper vs. lower bound)
			}
			if (existing.getBareConstant().equals(polyRel.getBareConstant())) {
				return existing;
			}
		}
		return null;
	}

	protected final boolean addNonPolynomial(final Term nonPolynomial) {
		if (mInconsistent) {
			throw new AssertionError("must not add if already inconsistent");
		}
		final Term neg = SmtUtils.unzipNot(nonPolynomial);
		boolean result;
		if (neg != null) {
			result = addNegative(neg);
		} else {
			result = addPositive(nonPolynomial);
		}
		return result;
	}

	protected Check checkNegative(final Term term) {
		Check result;
		if (mNegative.contains(term)) {
			assert (!mPositive.contains(term));
			result = Check.REDUNDANT;
		} else if (mPositive.contains(term)) {
			result = Check.INCONSISTENT;
		} else {
			result = Check.MAYBE_USEFUL;
		}
		return result;
	}

	private final boolean addNegative(final Term term) {
		final Check check = checkNegative(term);
		boolean result;
		switch (check) {
		case INCONSISTENT:
			result = true;
			break;
		case MAYBE_USEFUL:
			mNegative.add(term);
			result = false;
			break;
		case REDUNDANT:
			result = false;
			break;
		default:
			throw new AssertionError("unknown value " + check);
		}
		return result;
	}

	protected Check checkPositive(final Term term) {
		Check result;
		if (mPositive.contains(term)) {
			assert (!mNegative.contains(term));
			result = Check.REDUNDANT;
		} else if (mNegative.contains(term)) {
			result = Check.INCONSISTENT;
		} else {
			result = Check.MAYBE_USEFUL;
		}
		return result;
	}

	private final boolean addPositive(final Term term) {
		final Check check = checkPositive(term);
		boolean result;
		switch (check) {
		case INCONSISTENT:
			result = true;
			break;
		case MAYBE_USEFUL:
			mPositive.add(term);
			result = false;
			break;
		case REDUNDANT:
			result = false;
			break;
		default:
			throw new AssertionError("unknown value " + check);
		}
		return result;
	}

	public final Term and() {
		if (mInconsistent) {
			return mScript.term("false");
		}
		final List<Term> params = new ArrayList<>();
		for (final Entry<Map<?, Rational>, PolynomialRelation> pair : mPolyRels.getSetOfPairs()) {
			params.add(pair.getValue().toTerm(mScript));
		}
		for (final Entry<Term, BitvectorInequalityRelation> pair : mBvInequalityRels.getSetOfPairs()) {
			params.add(pair.getValue().toTerm(mScript));
		}
		for (final BitvectorInequalityRelation rel : mCompoundBvInequalityRels) {
			params.add(rel.toTerm(mScript));
		}
		params.addAll(mPositive);
		for (final Term term : mNegative) {
			params.add(SmtUtils.not(mScript, term));
		}
		return SmtUtils.and(mScript, params);
	}

	public final Term or() {
		if (mInconsistent) {
			return mScript.term("true");
		}
		final List<Term> params = new ArrayList<>();
		for (final Entry<Map<?, Rational>, PolynomialRelation> pair : mPolyRels.getSetOfPairs()) {
			params.add(pair.getValue().negate().toTerm(mScript));
		}
		for (final Entry<Term, BitvectorInequalityRelation> pair : mBvInequalityRels.getSetOfPairs()) {
			params.add(pair.getValue().negate().toTerm(mScript));
		}
		for (final BitvectorInequalityRelation rel : mCompoundBvInequalityRels) {
			params.add(rel.negate().toTerm(mScript));
		}
		for (final Term term : mPositive) {
			params.add(SmtUtils.not(mScript, term));
		}
		params.addAll(mNegative);
		return SmtUtils.or(mScript, params);
	}

}
