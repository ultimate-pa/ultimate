/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


public class CompositeReason extends LAReason {
	private final LAReason[] mReasons;
	private final Rational[] mCoeffs;
	private final InfinitNumber mExactBound;

	public CompositeReason(LinVar var, InfinitNumber bound, boolean isUpper,
			LAReason[] reasons, Rational[] coeffs, LiteralReason lastLiteral) {
		super(var, bound, isUpper, lastLiteral);
		assert (lastLiteral != null);
		mReasons = reasons;
		mCoeffs = coeffs;
		mExactBound = bound;
		if (var.mIsInt) {
			if (isUpper) {
				mBound = bound.floor();
			} else {
				mBound = bound.ceil();
			}
		} else {
			mBound = bound;
		}
		assert (!getVar().mIsInt || mBound.isIntegral());
	}
		
	@Override
	public InfinitNumber getExactBound() {
		return mExactBound;
	}
	
	@Override
	InfinitNumber explain(Explainer explainer,
			InfinitNumber slack, Rational factor) {
		// First check, if there is already a literal with a weaker bound
		// that is strong enough to explain the conflict/unit clause.  
		// However, make sure that this literal was set before the literal
		// for which we want to generate a unit clause.
		//
		// needToExplain is set to true, if there is a weaker literal
		// that was not set before the current conflict/unit clause.  Usually,
		// this means that we want to generate a unit clause for such a 
		// weaker literal.  Therefore, it does not make sense to create a
		// composite literal.
		boolean needToExplain = false;
		if (isUpper()) {
			final Entry<InfinitNumber, BoundConstraint> nextEntry = 
				getVar().mConstraints.ceilingEntry(getBound());
			if (nextEntry != null) {
				final BoundConstraint nextBound = nextEntry.getValue();
				if (nextBound.getDecideStatus() == nextBound
					&& explainer.canExplainWith(nextBound)) {
					final InfinitNumber diff = nextBound.getBound().sub(getBound());
					if (slack.compareTo(diff) > 0) {
						explainer.addLiteral(nextBound.negate(), factor);
						return slack.sub(diff);
					}
				} else {
					needToExplain = true;
				}
			}
		} else {
			final Entry<InfinitNumber, BoundConstraint> nextEntry = 
				getVar().mConstraints.lowerEntry(getBound());
			if (nextEntry != null) {
				final BoundConstraint nextBound = nextEntry.getValue();
				if (nextBound.getDecideStatus() == nextBound.negate()
					&& explainer.canExplainWith(nextBound)) {
					final InfinitNumber diff =
							getBound().sub(nextBound.getInverseBound());
					if (slack.compareTo(diff) > 0) {
						explainer.addLiteral(nextBound, factor);
						return slack.sub(diff);
					}
				} else {
					needToExplain = true;
				}
			}
		}
		
		final InfinitNumber diff = !getVar().mIsInt ? InfinitNumber.ZERO // NOPMD
				: isUpper()
				? mExactBound.sub(getBound())
				: getBound().sub(mExactBound);
		final int decideLevel = explainer.getDecideLevel();
		// Should we create a composite literal?  We do this only, if there
		// is not already a weaker usable bound (needToExplain is true), and
		// if we do not have enough slack to avoid the composite literal 
		// completely or if the composite literal would appear on the same
		// decideLevel (and therefore would be immediately removed anyway).
		if (needToExplain
			|| (slack.compareTo(diff) > 0
			 && getLastLiteral().getDecideLevel() >= decideLevel)) {
			// Here, we do not create a composite literal.
			final boolean enoughSlack = slack.compareTo(diff) > 0;
			if (!enoughSlack) {
				// we have not have enough slack to just use the proof of 
				// the exact bound. Create a sub-annotation.
				explainer.addAnnotation(this, factor);
				return slack;
			}
			// Just explain the exact bound using the reason array.
			slack = slack.sub(diff);
			assert (slack.compareTo(InfinitNumber.ZERO) > 0);
			for (int i = 0; i < mReasons.length; i++) {
				final Rational coeff = mCoeffs[i];
				slack = slack.div(coeff.abs());
				slack = mReasons[i].explain(explainer, 
						slack, factor.mul(coeff));
				slack = slack.mul(coeff.abs());
				assert (slack.compareTo(InfinitNumber.ZERO) > 0);
			}
			return slack;
		}
		final Literal lit = explainer.createComposite(this);
		assert (lit.getAtom().getDecideStatus() == lit);
		explainer.addLiteral(lit.negate(), factor);
		return slack;
	}
}
