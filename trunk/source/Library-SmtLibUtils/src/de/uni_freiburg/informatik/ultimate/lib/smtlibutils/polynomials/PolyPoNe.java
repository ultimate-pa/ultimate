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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AbstractGeneralizedAffineTerm.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Internal data structure that we use to construct simplified conjunctions and
 * disjunction. We distinguish three kinds of parameters of the
 * disjunction/conjunction.
 * <li>polynomial parameter: params that can be converted into a
 * {@link PolynomialRelation}
 * <li>negative parameters: params that cannot be converted into a
 * {@link PolynomialRelation} and are negated
 * <li>negative parameters: all other params.
 *
 * Based on a pairwise comparison of params, we decide whether a parameter is
 * redundant and can be omitted or whether the result for two parameters is
 * already the absorbing element of the operation.
 *
 * For disjunctions we store negated versions of the
 * {@link PolynomialRelation}s, apply the rules for conjunctions, and negate all
 * {@link PolynomialRelation} before computing the result.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolyPoNe {

	protected enum Check {
		REDUNDANT, INCONSISTENT, MAYBE_USEFUL, FUSIBLE
	};

	protected final Script mScript;
	private final Set<Term> mPositive = new HashSet<>();
	private final Set<Term> mNegative = new HashSet<>();
	private final HashRelation<Map<?, Rational>, PolynomialRelation> mPolyRels = new HashRelation<>();
	private boolean mInconsistent = false;

	PolyPoNe(final Script script) {
		mScript = script;
	}

	public boolean isInconsistent() {
		return mInconsistent;
	}

	void add(final Collection<Term> params, final boolean negate) {
		for (final Term param : params) {
			// TODO 20201123 Matthias: For bitvectors distinct and equality are polynomial,
			// the other inequalities not, hence distinct and equality should also be added
			// as nonPoly. Add another data structure for binary relations
			final PolynomialRelation polyPolyRel;
			if (negate) {
				polyPolyRel = PolynomialRelation.of(mScript, param, TransformInequality.NONSTRICT2STRICT);
			} else {
				polyPolyRel = PolynomialRelation.of(mScript, param, TransformInequality.STRICT2NONSTRICT);
			}
			if (polyPolyRel != null) {
				final PolynomialRelation addedRel = negate ? polyPolyRel.negate(mScript) : polyPolyRel;
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

	protected Check checkPolyRel(final Script script, final PolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Check res1 = compareToExistingRepresentations(newPolyRel, removeExpliedPolyRels);
		if (res1 == Check.INCONSISTENT || res1 == Check.REDUNDANT) {
			return res1;
		}
		assert res1 == null || res1 == Check.FUSIBLE;
		final PolynomialRelation alternativeRepresentation = newPolyRel.mul(mScript, Rational.MONE);
		final Check res2 = compareToExistingRepresentations(alternativeRepresentation, removeExpliedPolyRels);
		if (res2 == Check.INCONSISTENT || res2 == Check.REDUNDANT) {
			return res2;
		}
		assert res2 == null || res2 == Check.FUSIBLE;
		if (res1 == Check.FUSIBLE || res2 == Check.FUSIBLE) {
			return Check.FUSIBLE;
		} else {
			return Check.MAYBE_USEFUL;
		}
	}

	private Check compareToExistingRepresentations(final PolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Set<PolynomialRelation> existingPolyRels = mPolyRels
				.getImage(newPolyRel.getPolynomialTerm().getAbstractVariable2Coefficient());
		final List<PolynomialRelation> existingThatExplyNew = new ArrayList<>();
		boolean isFusible = false;
		for (final PolynomialRelation existingPolyRel : existingPolyRels) {
			final ComparisonResult comp = AbstractGeneralizedAffineTerm.compareRepresentation(existingPolyRel,
					newPolyRel);
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
				case FUSIBLE:
					// If this PolynomialRelation can be fused, we will change its relation symbol
					// and hence this changed PolynomialRelation explies the existing
					// PolynomialRelation. If the newPolyRel is fusible it can still exply others.
					// However, it must not be implied by others. If it would be implied by others
					// the existing relations would be inconsistent or have been fused already.
					// (One may wonder: is it really safe to remove the existingPolyRel? Couldn't it
					// happen that we never add the fused relation? The arguments above explain that
					// the removal is safe.)
					if (removeExpliedPolyRels) {
						existingThatExplyNew.add(existingPolyRel);
					}
					isFusible = true;
					break;
				default:
					throw new AssertionError("unknown value " + comp);
				}
			}
		}
		if (removeExpliedPolyRels) {
			// remove all existing relations that exply the new relation (i.e., all that are
			// implied by the new relation)
			for (final PolynomialRelation existing : existingThatExplyNew) {
				final boolean modified = mPolyRels.removePair(existing.getPolynomialTerm().getAbstractVariable2Coefficient(),
						existing);
				assert modified : "nothing removed";
			}
		}
		if (isFusible) {
			return Check.FUSIBLE;
		} else {
			return null;
		}
	}

	protected final boolean addPolyRel(final Script script, final PolynomialRelation polyRel,
			final boolean removeExpliedPolyRels) {
		if (mInconsistent) {
			throw new AssertionError("must not add if already inconsistent");
		}
		final Check check = checkPolyRel(script, polyRel, removeExpliedPolyRels);
		if (check == Check.FUSIBLE) {
			assert polyRel.getRelationSymbol() == RelationSymbol.LEQ || polyRel.getRelationSymbol() == RelationSymbol.GEQ;
			final PolynomialRelation fusedPolyRel = PolynomialRelation.of(polyRel.getPolynomialTerm(), RelationSymbol.EQ);
			mPolyRels.addPair(polyRel.getPolynomialTerm().getAbstractVariable2Coefficient(), fusedPolyRel);
			return false;
		} else if (check == Check.MAYBE_USEFUL) {
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
		for (final Term term : mPositive) {
			params.add(term);
		}
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
			params.add(pair.getValue().negate(mScript).toTerm(mScript));
		}
		for (final Term term : mPositive) {
			params.add(SmtUtils.not(mScript, term));
		}
		for (final Term term : mNegative) {
			params.add(term);
		}
		return SmtUtils.or(mScript, params);
	}

}
