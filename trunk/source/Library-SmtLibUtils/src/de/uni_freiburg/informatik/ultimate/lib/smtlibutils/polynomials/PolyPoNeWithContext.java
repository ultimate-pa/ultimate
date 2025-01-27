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

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolyPoNeWithContext extends PolyPoNe {
	final PolyPoNe mContext;

	PolyPoNeWithContext(final Script script, final Junction junction, final PolyPoNe context) {
		super(script, junction);
		if (context.isInconsistent()) {
			throw new AssertionError("must not add inconsistent context");
		}
		mContext = context;
	}

	Term and(final Term context, final List<Term> params) {
		if (SmtUtils.isFalseLiteral(context)) {
			return mScript.term("false");
		}
		return and(Arrays.asList(SmtUtils.getConjuncts(context)), params);
	}

	private Term and(final Collection<Term> contextConjuncts, final List<Term> params) {
		addContext(contextConjuncts);
		return super.and(params);
	}

	Term or(final Term context, final List<Term> params) {
		if (SmtUtils.isFalseLiteral(context)) {
			return mScript.term("true");
		}
		// warning: context is always conjunctive
		return or(Arrays.asList(SmtUtils.getConjuncts(context)), params);
	}

	private Term or(final Collection<Term> contextConjuncts, final List<Term> params) {
		addContext(contextConjuncts);
		return super.or(params);
	}

	private boolean addContext(final Collection<Term> contextParams) {
		for (final Term param : contextParams) {
			final PolynomialRelation polyRel = PolynomialRelation.of(mScript, param,
					TransformInequality.STRICT2NONSTRICT);
			if (polyRel != null) {
				final boolean isInconsistent = mContext.addPolyRel(mScript, polyRel, true);
				if (isInconsistent) {
					return true;
				}
			} else {
				final boolean isInconsistent = mContext.addNonPolynomial(param);
				if (isInconsistent) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	protected final boolean addPolyRel(final Script script, final PolynomialRelation polyRel,
			final boolean removeExpliedPolyRels) {
		if (isInconsistent()) {
			throw new AssertionError("must not add if already inconsistent");
		}

		final Check check = mContext.checkPolyRel(script, polyRel, false);
		if (check == Check.MAYBE_USEFUL) {
			final PolynomialRelation polyToAdd = tryToFuseWithContext(polyRel);
			return super.addPolyRel(script, polyToAdd, removeExpliedPolyRels);
		} else if (check == Check.REDUNDANT) {
			return false;
		} else if (check == Check.INCONSISTENT) {
			return true;
		} else {
			throw new AssertionError("unknown value " + check);
		}
	}

	/**
	 * If we can fuse this {@link PolynomialRelation} with a
	 * {@link PolynomialRelation} from the context we return the result of the
	 * fusion. Otherwise, we return the input.
	 */
	public PolynomialRelation tryToFuseWithContext(final PolynomialRelation polyRel) {
		if (!polyRel.getRelationSymbol().isConvexInequality()) {
			// we can only fuse inequalities
			return polyRel;
		}
		final PolynomialRelation originalNonstrictInput;
		// For disjunctions, we work with negated polynomial relations,
		// hence we have to negate again to get the original input.
		if (mJunction == Junction.OR) {
			// Important: Integer relations in context are non-strict, we have to make this
			// also non-strict for checking fusibility.
			originalNonstrictInput = polyRel.negate().tryToConvertToEquivalentNonStrictRelation();
		} else {
			assert !polyRel.getRelationSymbol().isStrictRelation()
					|| !SmtSortUtils.isIntSort(polyRel.getPolynomialTerm().getSort())
					: "Inequalities in conjunctions are non-strict";
			originalNonstrictInput = polyRel;
		}
		// Since context is a conjunction we always have to use Junction.AND
		final PolynomialRelation fusionPartner = mContext.isFusibleWithExistingRelations(mScript, Junction.AND,
				originalNonstrictInput);
		final PolynomialRelation result;
		if (fusionPartner == null) {
			// no fusion possible
			result = polyRel;
		} else {
			final PolynomialRelation fused;
			if (mJunction == Junction.OR) {
				// For disjunctions we work with negated relations, hence we store
				// RelationSymbol.DISTINCT although the final result will contain
				// RelationSymbol.EQ
				fused = PolynomialRelation.of(originalNonstrictInput.getPolynomialTerm(), RelationSymbol.DISTINCT);
			} else {
				assert mJunction == Junction.AND;
				fused = PolynomialRelation.of(originalNonstrictInput.getPolynomialTerm(), RelationSymbol.EQ);
			}
			result = fused;
		}
		return result;
	}

	@Override
	protected Check checkNegative(final Term term) {
		final Check contextCheck = mContext.checkNegative(term);
		if (contextCheck != Check.MAYBE_USEFUL) {
			return contextCheck;
		} else {
			return super.checkNegative(term);
		}
	}

	@Override
	protected Check checkPositive(final Term term) {
		final Check contextCheck = mContext.checkPositive(term);
		if (contextCheck != Check.MAYBE_USEFUL) {
			return contextCheck;
		} else {
			return super.checkPositive(term);
		}
	}

}
