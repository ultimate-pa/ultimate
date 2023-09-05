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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolyPoNeWithContext extends PolyPoNe {
	final PolyPoNe mContext;

	PolyPoNeWithContext(final Script script, final PolyPoNe context) {
		super(script);
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
			final PolynomialRelation polyRel = PolynomialRelation.of(mScript, param);
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
	protected Check checkPolyRel(final Script script, final PolynomialRelation newPolyRel,
			final boolean removeExpliedPolyRels) {
		final Check contextCheck = mContext.checkPolyRel(script, newPolyRel, false);
		if (contextCheck == Check.INCONSISTENT || contextCheck == Check.REDUNDANT) {
			return contextCheck;
		} else {
			if (contextCheck == Check.MAYBE_USEFUL) {
				return super.checkPolyRel(mScript, newPolyRel, true);
			} else {
				assert contextCheck == Check.FUSIBLE;
				assert newPolyRel.getRelationSymbol() == RelationSymbol.LEQ
						|| newPolyRel.getRelationSymbol() == RelationSymbol.GEQ;
				final PolynomialRelation fusedPolyRel = PolynomialRelation.of(newPolyRel.getPolynomialTerm(),
						RelationSymbol.EQ);
				final Check check = super.checkPolyRel(mScript, fusedPolyRel, true);
				if (check == Check.INCONSISTENT || check == Check.REDUNDANT) {
					return check;
				} else {
					// Cannot be Check.FUSIBLE otherwise the counterpart for the fuse would be in
					// context and here.
					assert check == Check.MAYBE_USEFUL : "Cannot be fusible";
					return Check.FUSIBLE;
				}
			}
		}
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
