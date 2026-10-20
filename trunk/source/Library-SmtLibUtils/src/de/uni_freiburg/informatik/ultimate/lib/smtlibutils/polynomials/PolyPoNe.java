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
import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Internal data structure that we use to construct simplified conjunctions and disjunctions. We distinguish three
 * kinds of parameters of the disjunction/conjunction.
 * <ul>
 * <li>polynomial parameter: params that can be converted into a {@link IPolynomialRelation}
 * <li>negative parameters: params that cannot be converted into a {@link IPolynomialRelation} and are negated
 * <li>positive parameters: all other params.
 * </ul>
 *
 * Based on a pairwise comparison of params, we decide whether a parameter is redundant and can be omitted or whether
 * the result for two parameters is already the absorbing element of the operation.
 *
 * For disjunctions we store negated versions of the {@link IPolynomialRelation}s, apply the rules for conjunctions, and
 * negate all {@link IPolynomialRelation} before computing the result.
 * <p>
 * <b>Bitvector inequalities.</b> Bitvector inequalities ({@code bvult}, {@code bvule}, {@code bvslt}, {@code bvsle}
 * and their "greater" counterparts) cannot be a {@link PolynomialRelation}, see {@link BitvectorInequalityRelation}.
 * {@link #add} therefore first asks the shared factory {@code IPolynomialRelation.of} and, if that returns
 * {@code null}, builds a {@link BitvectorInequalityRelation} itself. Relations with a constant on exactly one side
 * are kept in {@code mBvInequalityRels}, next to {@code mPolyRels}, keyed by the other side. The key is the bare
 * variable or, for example for {@code x + y <=u 5}, the whole expression including its offset. Only relations with
 * the same key are compared. All other relations, for example {@code x <=u y}, are never compared. They are handled
 * like every other parameter that is not a polynomial relation and become positive parameters.
 * <p>
 * A new relation is compared with the stored relations under the same key. Both are first brought to an "effective
 * inclusive boundary" ({@code x <u 9} behaves like {@code x <=u 8}). Relations with different signedness, or whose
 * boundary would overflow or underflow, are not compared. Two bounds in the same direction: the tighter one wins, the
 * looser one is dropped or not added. Two bounds in opposite directions: if no value is left between them, the
 * conjunction is inconsistent. Examples:
 * <ul>
 * <li>{@code x <=u 7 and x <u 9} gives {@code x <=u 7}
 * <li>{@code x >=u 10 and x <=u 5} is inconsistent, i.e. {@code false}
 * <li>{@code x <=u 5 and x >=u 5} is fused to {@code x = 5}
 * </ul>
 * Bounds also interact with other facts in {@code mPolyRels}:
 * <ul>
 * <li>A known equality that fixes the value of the non-constant side (for example {@code x = c}, stored as
 * {@code x = c} or as {@code c = x}, or {@code x + y = 7} for a bound on {@code x + y + 2}) makes a bound redundant if
 * that value satisfies it and inconsistent if not. This works in both orders: an equality that is added after a
 * bound drops the bound or makes the conjunction inconsistent.
 * <li>A disequality such as {@code x != c} together with a bound whose effective boundary is {@code c} gives the
 * strict bound:
 * {@code x != 3 and x <=u 3} is {@code x <u 3}. If no value is left, e.g. for {@code x != 0 and x <=u 0}, the
 * conjunction is inconsistent.
 * </ul>
 * The same fact can be written as a bound on an expression or as a bound on its bitwise complement. The
 * {@link PolynomialTermTransformer} reads {@code bvneg x} as {@code -x} and {@code bvnot x} as {@code -x-1}, so such
 * relations get the expression as key. To let a new relation meet a stored fact that is written the other way round,
 * the new relation is also compared in its alternative spelling (see
 * {@link BitvectorInequalityRelation#constructAlternativeRepresentation}), which has a different key. This is
 * analogous to {@link #checkPolyRel}, which compares a new relation and its multiple with {@code -1}. Example:
 * {@code (bvnot x) <=u 100} means {@code x >=u 155}, which contradicts a stored {@code x <=u 5}.
 * <p>
 * Disjunctions use these rules on the negated relations: {@code x <=u 10 or x >=u 5} is {@code true}, because
 * {@code x >u 10 and x <u 5} leaves no value. {@link PolyPoNeWithContext} compares a new relation with the relations
 * of its context in the same way, but read-only (see {@link #checkBvInequalityRel}).
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
	private final HashRelation<Map<?, Rational>, IPolynomialRelation> mPolyRels = new HashRelation<>();
	/**
	 * Bitvector-inequality analogue of {@link #mPolyRels}, for relations with a constant on one side (for example
	 * {@code x <=u 5} or {@code x + y <=u 5}). Keyed by the other side: the bare variable, or the whole expression
	 * including its offset, since there is no single combined polynomial to key on the way {@link #mPolyRels} does.
	 * Relations with the same key are compared by their constants. See {@link BitvectorInequalityRelation}.
	 */
	private final HashRelation<Term, BitvectorInequalityRelation> mBvInequalityRels = new HashRelation<>();
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
			IPolynomialRelation polyPolyRel;
			if (negate) {
				polyPolyRel = IPolynomialRelation.of(mScript, param, TransformInequality.NONSTRICT2STRICT);
			} else {
				polyPolyRel = IPolynomialRelation.of(mScript, param, TransformInequality.STRICT2NONSTRICT);
			}
			if (polyPolyRel == null) {
				// The shared factory never builds a BitvectorInequalityRelation (subtracting both sides is unsound for
				// bitvector inequalities), so PolyPoNe builds it itself. Moving this into the shared factory would
				// change the behavior for every other caller of IPolynomialRelation.of.
				polyPolyRel = BitvectorInequalityRelation.of(mScript, param);
			}
			if (polyPolyRel != null) {
				final IPolynomialRelation addedRel = negate ? polyPolyRel.negate() : polyPolyRel;
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

	protected final Check checkPolyRel(final Script script, final IPolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Check res1 = compareToExistingRepresentations(newPolyRel, removeExpliedPolyRels);
		if (res1 == Check.INCONSISTENT || res1 == Check.REDUNDANT) {
			return res1;
		}
		assert res1 == null;
		final IPolynomialRelation alternativeRepresentation = newPolyRel.mul(mScript, Rational.MONE);
		final Check res2 = compareToExistingRepresentations(alternativeRepresentation, removeExpliedPolyRels);
		if (res2 == Check.INCONSISTENT || res2 == Check.REDUNDANT) {
			return res2;
		}
		assert res2 == null;
		return Check.MAYBE_USEFUL;
	}

	/**
	 * Read-only counterpart of {@link #addBvInequalityRel} for {@link PolyPoNeWithContext}: compares {@code polyRel}
	 * with what is stored here, but stores nothing. Needed because {@link #checkPolyRel} calls
	 * {@code getPolynomialTerm()}, which a {@link BitvectorInequalityRelation} does not have.
	 */
	protected final Check checkBvInequalityRel(final BitvectorInequalityRelation polyRel) {
		final BitvectorInequalityRelation.PolynomialAndConstant shape =
				polyRel.asPolynomialVsConstant(mScript);
		if (shape == null) {
			// There is no constant on exactly one side (e.g. x <=u y), so there is no key to look this relation up
			// by. We do not compare such relations.
			return Check.MAYBE_USEFUL;
		}
		// Compare with the stored facts that have the same key, i.e. that are about the same expression, and with
		// those under the key of the alternative spelling.
		return compareWithStoredAndAlternative(polyRel, shape.getKey(), null);
	}

	private Check compareToExistingRepresentations(final IPolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Set<IPolynomialRelation> existingPolyRels =
				mPolyRels.getImage(newPolyRel.getPolynomialTerm().getAbstractVariable2Coefficient());
		final List<IPolynomialRelation> existingThatExplyNew = new ArrayList<>();
		for (final IPolynomialRelation existingPolyRel : existingPolyRels) {
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
			for (final IPolynomialRelation existing : existingThatExplyNew) {
				final boolean modified =
						mPolyRels.removePair(existing.getPolynomialTerm().getAbstractVariable2Coefficient(), existing);
				assert modified : "nothing removed";
			}
		}
		return null;
	}

	protected IPolynomialRelation isFusibleWithExistingRelations(final Script script, final Junction junction,
			final IPolynomialRelation newPolyRel) {
		final IPolynomialRelation res1 = isFusibleWithExistingRepresentation(junction, newPolyRel);
		if (res1 != null) {
			return res1;
		}
		final IPolynomialRelation alternativeRepresentation = newPolyRel.mul(mScript, Rational.MONE);
		final IPolynomialRelation res2 = isFusibleWithExistingRepresentation(junction, alternativeRepresentation);
		if (res2 != null) {
			return res2;
		}
		return null;
	}

	private IPolynomialRelation isFusibleWithExistingRepresentation(final Junction junction,
			final IPolynomialRelation newPolyRel) {
		final Set<IPolynomialRelation> existingPolyRels =
				mPolyRels.getImage(newPolyRel.getPolynomialTerm().getAbstractVariable2Coefficient());
		for (final IPolynomialRelation existingPolyRel : existingPolyRels) {
			final boolean res =
					AbstractGeneralizedAffineTerm.areRepresentationsFusible(junction, existingPolyRel, newPolyRel);
			if (res) {
				return existingPolyRel;
			}
		}
		return null;
	}

	protected boolean addPolyRel(final Script script, final IPolynomialRelation polyRel,
			final boolean removeExpliedPolyRels) {
		if (mInconsistent) {
			throw new AssertionError("must not add if already inconsistent");
		}
		if (polyRel instanceof BitvectorInequalityRelation) {
			// Never call getPolynomialTerm() on a BitvectorInequalityRelation - it has no single polynomial term
			// (see BitvectorInequalityRelation.getPolynomialTerm()'s javadoc). Handled entirely separately below,
			// see addBvInequalityRel.
			return addBvInequalityRel((BitvectorInequalityRelation) polyRel);
		}

		final Check check = checkPolyRel(script, polyRel, removeExpliedPolyRels);
		if (check == Check.MAYBE_USEFUL) {
			if (polyRel.getRelationSymbol().isConvexInequality()) {
				final IPolynomialRelation fusionPartner = isFusibleWithExistingRelations(mScript, Junction.AND, polyRel);
				if (fusionPartner != null) {
					mPolyRels.removePair(fusionPartner.getPolynomialTerm().getAbstractVariable2Coefficient(),
							fusionPartner);
					final IPolynomialRelation fusion =
							IPolynomialRelation.of(polyRel.getPolynomialTerm(), RelationSymbol.EQ);
					mPolyRels.addPair(fusion.getPolynomialTerm().getAbstractVariable2Coefficient(), fusion);
					return dropBvInequalitiesContradictingNewEquality(fusion);
				}
			}
			mPolyRels.addPair(polyRel.getPolynomialTerm().getAbstractVariable2Coefficient(), polyRel);
			return polyRel.getRelationSymbol() == RelationSymbol.DISTINCT ? fuseNewDistinctWithBvBound(polyRel)
					: dropBvInequalitiesContradictingNewEquality(polyRel);
		} else if (check == Check.REDUNDANT) {
			return false;
		} else if (check == Check.INCONSISTENT) {
			return true;
		} else {
			throw new AssertionError("unknown value " + check);
		}
	}

	/**
	 * Cross-checks an equality just added to {@link #mPolyRels} against any bitvector-inequality bounds already
	 * known for the same variables in {@link #mBvInequalityRels} - the mirror direction of
	 * {@link #compareWithStored}, which only handles a new inequality checked against a known equality. A bound
	 * the equality's value violates makes the whole conjunction inconsistent; a bound it satisfies is now redundant
	 * (the equality is strictly more precise) and gets dropped. A no-op if {@code polyRel} isn't a bitvector equality.
	 */
	private boolean dropBvInequalitiesContradictingNewEquality(final IPolynomialRelation polyRel) {
		if (polyRel.getRelationSymbol() != RelationSymbol.EQ
				|| !SmtSortUtils.isBitvecSort(polyRel.getPolynomialTerm().getSort())) {
			return false;
		}
		for (final Entry<BitvectorInequalityRelation, BitvectorConstant> boundAndValue : boundsAbout(polyRel)) {
			final BitvectorInequalityRelation bound = boundAndValue.getKey();
			if (!satisfiesBound(boundAndValue.getValue(), bound)) {
				// The expression has to have this value, but a stored bound forbids it: contradiction.
				return true;
			}
			// The bound holds for this value, so it adds nothing now that the exact value is known.
			mBvInequalityRels.removePair(bound.asPolynomialVsConstant(mScript).getKey(), bound);
		}
		return false;
	}

	/**
	 * Bitvector-inequality analogue of {@link #addPolyRel} for relations with a constant on one side (see
	 * {@link BitvectorInequalityRelation#isPolynomialVsConstant()}). The new relation is compared with the stored
	 * relations under the same key, with the stored relations under the key of its alternative spelling, and with known
	 * equalities and disequalities, and is then stored. Relations without a constant on
	 * exactly one side are not compared, they become positive parameters.
	 * <p>
	 * The <i>key</i> is the side of the relation that is not the constant: the variable {@code x} for
	 * {@code x <=u 5}, or the whole expression for {@code x + y <=u 5}. Two relations with the same key talk about
	 * the same unknown value, so they can be compared by just comparing their constants. Relations with different
	 * keys cannot say anything about each other and are never compared.
	 *
	 * @return {@code true} iff adding the relation made the whole conjunction inconsistent
	 */
	private boolean addBvInequalityRel(final BitvectorInequalityRelation polyRel) {
		final BitvectorInequalityRelation.PolynomialAndConstant shape =
				polyRel.asPolynomialVsConstant(mScript);
		if (shape == null) {
			// No constant on exactly one side (e.g. x <=u y), so there is no key to look the relation up by.
			// Comparing it would mean scanning all stored relations, so we treat it as an opaque parameter.
			return addNonPolynomial(polyRel.toTerm(mScript));
		}
		final Term variable = shape.getKey();
		// Compare with all stored facts about the same key (bounds and known equalities). Stored relations that become
		// redundant are only collected here and removed after the loop, because we iterate over the stored relations.
		final List<BitvectorInequalityRelation> explied = new ArrayList<>();
		final Check check = compareWithStoredAndAlternative(polyRel, variable, explied);
		if (check == Check.REDUNDANT) {
			return false;
		}
		if (check == Check.INCONSISTENT) {
			return true;
		}
		// Now we know the new relation is kept, so the stored relations that it makes redundant can be removed.
		for (final BitvectorInequalityRelation existing : explied) {
			mBvInequalityRels.removePair(existing.asPolynomialVsConstant(mScript).getKey(), existing);
		}
		// An upper and a lower bound with the same constant (x <=u 5 and x >=u 5) are the equality x = 5.
		final BitvectorInequalityRelation fusionPartner = findFusibleBvInequality(variable, polyRel);
		if (fusionPartner != null) {
			// Insert the equality via the existing path for single-term relations.
			mBvInequalityRels.removePair(variable, fusionPartner);
			final IPolynomialRelation fusion = PolynomialRelation.of(mScript, RelationSymbol.EQ, variable,
					shape.getConstantTerm());
			return addPolyRel(mScript, fusion, true);
		}
		// A stored disequality next to a bound whose effective boundary is the excluded value tightens the bound to a
		// strict one (x != 3 and x <=u 3 is x <u 3).
		final BitvectorConstant boundary = effectiveInclusiveBoundary(polyRel);
		final IPolynomialRelation distinct = boundary == null ? null : findDistinctWithValue(polyRel, boundary);
		if (distinct != null) {
			mPolyRels.removePair(distinct.getPolynomialTerm().getAbstractVariable2Coefficient(), distinct);
			final BitvectorInequalityRelation strict = strictBoundAt(polyRel, boundary);
			// No strict bound means that no value is left: contradiction.
			return strict == null || addBvInequalityRel(strict);
		}
		// Nothing special applies, just remember the relation.
		mBvInequalityRels.addPair(variable, polyRel);
		return false;
	}

	/**
	 * Compares two {@link BitvectorInequalityRelation}s that have a constant on one side and share the same key (the
	 * same {@link HashRelation} bucket in {@link #mBvInequalityRels}). Handles mixed strictness (e.g.
	 * {@code x <=u 7} vs. {@code x <u 9}) by normalizing both to an "effective inclusive boundary" first - see
	 * {@link #effectiveInclusiveBoundary}. For an upper and a lower bound the result is
	 * {@link ComparisonResult#INCONSISTENT} if the lower bound lies above the upper bound (empty range), otherwise
	 * {@code null}. Also returns {@code null} if the signedness differs or normalizing either side would
	 * underflow/overflow (no verdict attempted).
	 */
	private static ComparisonResult compareBvInequalities(final BitvectorInequalityRelation existing,
			final BitvectorInequalityRelation newRel) {
		final boolean existingUnsigned = isUnsigned(existing.getRelationSymbol());
		if (existingUnsigned != isUnsigned(newRel.getRelationSymbol())) {
			// Unsigned and signed comparisons read the same bits as different numbers (11111111 is 255 unsigned but
			// -1 signed), so their constants cannot be compared.
			return null;
		}
		final BitvectorConstant existingBoundary = effectiveInclusiveBoundary(existing);
		final BitvectorConstant newBoundary = effectiveInclusiveBoundary(newRel);
		if (existingBoundary == null || newBoundary == null) {
			// Normalizing would underflow/overflow, we give no verdict rather than guess.
			return null;
		}
		if (existing.isVariableOnLhs() != newRel.isVariableOnLhs()) {
			// One upper and one lower bound: empty range if the lower one lies above the upper one.
			final BitvectorConstant upper = existing.isVariableOnLhs() ? existingBoundary : newBoundary;
			final BitvectorConstant lower = existing.isVariableOnLhs() ? newBoundary : existingBoundary;
			final boolean empty = existingUnsigned ? BitvectorConstant.bvult(upper, lower)
					: BitvectorConstant.bvslt(upper, lower);
			return empty ? ComparisonResult.INCONSISTENT : null;
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
	 * Looks for a stored equality in {@link #mPolyRels} that fixes the value of the non-constant side {@code P} of
	 * {@code polyRel} (for example {@code x + y + 2} in {@code x + y + 2 <=u 5}), and returns that value, or
	 * {@code null} if there is none. An equality {@code Q = 0} with the same variables and coefficients as {@code P}
	 * gives {@code P = c(P) - c(Q)}, one with the negated coefficients gives {@code P = c(P) + c(Q)}, where {@code c}
	 * is the constant part. Equalities pin the value exactly, so this is also correct if the numbers wrap around.
	 */
	private BitvectorConstant findKnownValueOfExpression(final BitvectorInequalityRelation polyRel) {
		final AbstractGeneralizedAffineTerm<?> expression = nonConstantSide(polyRel);
		for (final IPolynomialRelation existing : polyRelsAbout(expression)) {
			if (existing.getRelationSymbol() == RelationSymbol.EQ) {
				return valueFixedBy(expression, existing);
			}
		}
		return null;
	}

	/**
	 * Finds a stored disequality in {@link #mPolyRels} that excludes exactly the value {@code value} of the
	 * non-constant side of {@code polyRel}, or {@code null} if there is none.
	 */
	private IPolynomialRelation findDistinctWithValue(final BitvectorInequalityRelation polyRel,
			final BitvectorConstant value) {
		final AbstractGeneralizedAffineTerm<?> expression = nonConstantSide(polyRel);
		for (final IPolynomialRelation existing : polyRelsAbout(expression)) {
			if (existing.getRelationSymbol() == RelationSymbol.DISTINCT
					&& value.equals(valueFixedBy(expression, existing))) {
				return existing;
			}
		}
		return null;
	}

	private static AbstractGeneralizedAffineTerm<?> nonConstantSide(final BitvectorInequalityRelation polyRel) {
		return polyRel.isVariableOnLhs() ? polyRel.getLhs() : polyRel.getRhs();
	}

	/**
	 * Returns the relations in {@link #mPolyRels} about exactly the same variables as {@code expression}. Looks in two
	 * buckets: "x = c" is stored under the shape {x:1}, but the constant-first "c = x" under {x:-1}.
	 */
	private List<IPolynomialRelation> polyRelsAbout(final AbstractGeneralizedAffineTerm<?> expression) {
		final AbstractGeneralizedAffineTerm<?> negated =
				(AbstractGeneralizedAffineTerm<?>) PolynomialTermOperations.mul(expression, Rational.MONE);
		final List<IPolynomialRelation> result = new ArrayList<>();
		result.addAll(mPolyRels.getImage(expression.getAbstractVariable2Coefficient()));
		result.addAll(mPolyRels.getImage(negated.getAbstractVariable2Coefficient()));
		return result;
	}

	/**
	 * Given a relation {@code Q = 0} or {@code Q != 0} over the same variables as {@code expression} {@code P}, returns
	 * the value of {@code P} that the relation fixes (for {@code =}) or excludes (for {@code !=}), or {@code null} if
	 * the variables differ. With the same coefficients {@code P = c(P) - c(Q)}, with negated coefficients
	 * {@code P = c(P) + c(Q)}, where {@code c} is the constant part. This is also correct if the numbers wrap around.
	 */
	private static BitvectorConstant valueFixedBy(final AbstractGeneralizedAffineTerm<?> expression,
			final IPolynomialRelation zeroRelation) {
		final Sort sort = expression.getSort();
		final AbstractGeneralizedAffineTerm<?> relationTerm = zeroRelation.getPolynomialTerm();
		final BitvectorConstant expressionConstant =
				BitvectorUtils.constructBitvectorConstant(expression.getConstant().numerator(), sort);
		final BitvectorConstant relationConstant =
				BitvectorUtils.constructBitvectorConstant(relationTerm.getConstant().numerator(), sort);
		if (expression.getAbstractVariable2Coefficient().equals(relationTerm.getAbstractVariable2Coefficient())) {
			return BitvectorConstant.bvsub(expressionConstant, relationConstant);
		}
		final AbstractGeneralizedAffineTerm<?> negated =
				(AbstractGeneralizedAffineTerm<?>) PolynomialTermOperations.mul(expression, Rational.MONE);
		if (negated.getAbstractVariable2Coefficient().equals(relationTerm.getAbstractVariable2Coefficient())) {
			return BitvectorConstant.bvadd(expressionConstant, relationConstant);
		}
		return null;
	}

	/**
	 * Returns the stored bounds in {@link #mBvInequalityRels} whose non-constant side has exactly the same variables
	 * as the relation {@code zeroRelation} (or the negated ones), together with the value of that side that
	 * {@code zeroRelation} fixes or excludes. The bounds are filed under their whole expression including the offset,
	 * so we cannot look them up by the variables and have to go through all of them.
	 */
	private List<Entry<BitvectorInequalityRelation, BitvectorConstant>> boundsAbout(
			final IPolynomialRelation zeroRelation) {
		final List<Entry<BitvectorInequalityRelation, BitvectorConstant>> result = new ArrayList<>();
		for (final Entry<Term, BitvectorInequalityRelation> pair : mBvInequalityRels.getSetOfPairs()) {
			final BitvectorInequalityRelation bound = pair.getValue();
			final BitvectorConstant value = valueFixedBy(nonConstantSide(bound), zeroRelation);
			if (value != null) {
				result.add(new SimpleEntry<>(bound, value));
			}
		}
		return result;
	}

	/**
	 * "x != c" together with a bound whose effective boundary is exactly c gives the strict bound at c ("x != 3 and
	 * x <= 3" is "x < 3"). Returns {@code null} if no value is left, e.g. for "x != 0 and x <=u 0".
	 */
	private BitvectorInequalityRelation strictBoundAt(final BitvectorInequalityRelation bound,
			final BitvectorConstant value) {
		final boolean unsigned = isUnsigned(bound.getRelationSymbol());
		final boolean upper = bound.isVariableOnLhs();
		final Sort sort = bound.getLhs().getSort();
		final BitvectorConstant extreme = upper ? BitvectorInequalityRelation.sortMin(sort, unsigned)
				: BitvectorInequalityRelation.sortMax(sort, unsigned);
		if (value.equals(extreme)) {
			// The only value the bound allowed was the excluded one, so no value is left.
			return null;
		}
		final RelationSymbol strict = unsigned ? RelationSymbol.BVULT : RelationSymbol.BVSLT;
		final Term key = bound.asPolynomialVsConstant(mScript).getKey();
		final Term constant = BitvectorUtils.constructTerm(mScript, value);
		return BitvectorInequalityRelation.of(mScript,
				upper ? strict.constructTerm(mScript, key, constant) : strict.constructTerm(mScript, constant, key));
	}

	/**
	 * Counterpart of the fusion in {@link #addBvInequalityRel} for a newly stored disequality: a bound already stored
	 * for the same expression whose effective boundary is exactly the excluded value becomes the strict bound at that
	 * value, and the disequality is dropped.
	 */
	private boolean fuseNewDistinctWithBvBound(final IPolynomialRelation distinct) {
		if (!SmtSortUtils.isBitvecSort(distinct.getPolynomialTerm().getSort())) {
			// Not a bitvector, so it has nothing to do with the stored bitvector bounds.
			return false;
		}
		for (final Entry<BitvectorInequalityRelation, BitvectorConstant> boundAndValue : boundsAbout(distinct)) {
			final BitvectorInequalityRelation bound = boundAndValue.getKey();
			if (boundAndValue.getValue().equals(effectiveInclusiveBoundary(bound))) {
				mBvInequalityRels.removePair(bound.asPolynomialVsConstant(mScript).getKey(), bound);
				mPolyRels.removePair(distinct.getPolynomialTerm().getAbstractVariable2Coefficient(), distinct);
				final BitvectorInequalityRelation strict = strictBoundAt(bound, boundAndValue.getValue());
				// No strict bound means that no value is left: contradiction.
				return strict == null || addBvInequalityRel(strict);
			}
		}
		return false;
	}

	/**
	 * Compares {@code polyRel} with the stored facts under {@code key}: a known equality that fixes the value of the
	 * non-constant side, and the stored bounds. If the new relation is stronger, the stored bounds it makes redundant
	 * are added to {@code explied} (may be {@code null} for a read-only check).
	 */
	private Check compareWithStored(final BitvectorInequalityRelation polyRel, final Term key,
			final List<BitvectorInequalityRelation> explied) {
		final BitvectorConstant knownValue = findKnownValueOfExpression(polyRel);
		if (knownValue != null) {
			// The known value satisfies the bound: redundant. It violates the bound: contradiction.
			return satisfiesBound(knownValue, polyRel) ? Check.REDUNDANT : Check.INCONSISTENT;
		}
		for (final BitvectorInequalityRelation existing : mBvInequalityRels.getImage(key)) {
			final ComparisonResult comp = compareBvInequalities(existing, polyRel);
			if (comp == null) {
				// No verdict (e.g. unsigned vs. signed), the two relations do not affect each other.
				continue;
			}
			switch (comp) {
			case IMPLIES:
			case EQUIVALENT:
				// The stored relation already says at least as much.
				return Check.REDUNDANT;
			case EXPLIES:
				// The new relation says more than the stored one. The stored one can be dropped.
				if (explied != null) {
					explied.add(existing);
				}
				break;
			case INCONSISTENT:
				return Check.INCONSISTENT;
			default:
				throw new AssertionError("unknown value " + comp);
			}
		}
		return Check.MAYBE_USEFUL;
	}

	/**
	 * Compares {@code polyRel} with the stored relations, first as it is and then in its alternative spelling (see
	 * {@link BitvectorInequalityRelation#constructAlternativeRepresentation}), which has a different key. Analogous to
	 * {@link #checkPolyRel}.
	 */
	private Check compareWithStoredAndAlternative(final BitvectorInequalityRelation polyRel, final Term key,
			final List<BitvectorInequalityRelation> explied) {
		final Check check = compareWithStored(polyRel, key, explied);
		if (check != Check.MAYBE_USEFUL) {
			return check;
		}
		final BitvectorInequalityRelation alternative = polyRel.constructAlternativeRepresentation();
		final BitvectorInequalityRelation.PolynomialAndConstant alternativeShape =
				alternative.asPolynomialVsConstant(mScript);
		if (alternativeShape == null) {
			// No constant on exactly one side, so there is no key to look the alternative spelling up by.
			return Check.MAYBE_USEFUL;
		}
		return compareWithStored(alternative, alternativeShape.getKey(), explied);
	}

	/** Does the concrete value {@code value} satisfy {@code rel}'s bound? */
	private static boolean satisfiesBound(final BitvectorConstant value, final BitvectorInequalityRelation rel) {
		final BitvectorConstant constant = rel.getBareConstant();
		final boolean unsigned = isUnsigned(rel.getRelationSymbol());
		final boolean strict = isStrict(rel.getRelationSymbol());
		if (rel.isVariableOnLhs()) {
			// Upper bound, the shape is "variable op constant", so we check "value op constant".
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
	private BitvectorInequalityRelation findFusibleBvInequality(final Term variable,
			final BitvectorInequalityRelation polyRel) {
		if (polyRel.getRelationSymbol() != RelationSymbol.BVULE && polyRel.getRelationSymbol() != RelationSymbol.BVSLE) {
			// Strict relations don't fuse into an equality.
			return null;
		}
		for (final BitvectorInequalityRelation existing : mBvInequalityRels.getImage(variable)) {
			if (existing.getRelationSymbol() != polyRel.getRelationSymbol()) {
				// Different symbol, e.g. unsigned vs. signed.
				continue;
			}
			if (existing.isVariableOnLhs() == polyRel.isVariableOnLhs()) {
				// We need opposite orientation: one upper bound and one lower bound.
				continue;
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
		for (final Entry<Map<?, Rational>, IPolynomialRelation> pair : mPolyRels.getSetOfPairs()) {
			params.add(pair.getValue().toTerm(mScript));
		}
		for (final Entry<Term, BitvectorInequalityRelation> pair : mBvInequalityRels.getSetOfPairs()) {
			params.add(pair.getValue().toTerm(mScript));
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
		for (final Entry<Map<?, Rational>, IPolynomialRelation> pair : mPolyRels.getSetOfPairs()) {
			params.add(pair.getValue().negate().toTerm(mScript));
		}
		for (final Entry<Term, BitvectorInequalityRelation> pair : mBvInequalityRels.getSetOfPairs()) {
			params.add(pair.getValue().negate().toTerm(mScript));
		}
		for (final Term term : mPositive) {
			params.add(SmtUtils.not(mScript, term));
		}
		params.addAll(mNegative);
		return SmtUtils.or(mScript, params);
	}

}
