/*
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayList;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * The Interpolator for linear arithmetic. This computes the interpolants with the algorithm described in "Proof Tree
 * Preserving Interpolation" in the version "newtechreport.pdf" in this repository. In particular we need to compute
 * leaf interpolants for trichotomy
 *
 * <pre>
 * a < b \/ a == b \/ a > b
 * </pre>
 *
 * and for simple conflicts with Farkas coefficients.
 *
 * @author Jochen Hoenicke, Alexander Nutz, Tanja Schindler
 */
public class LAInterpolator {

	Interpolator mInterpolator;
	/**
	 * The lemma for which we compute an interpolant.
	 */
	Term mLemma;
	/**
	 * The information needed to interpolate this lemma.
	 */
	InterpolatorClauseTermInfo mLemmaInfo = new InterpolatorClauseTermInfo();

	/**
	 * For each partition, this stores the partial interpolant.
	 */
	Interpolant[] mInterpolants;

	/**
	 * This is 1, if mSum is an integer, eps otherwise.
	 */
	InfinitNumber mEpsilon;

	/**
	 * Return the epsilon. This is 1 for integer constraints, eps for rational constraints.
	 *
	 * @return the epsilon.
	 */
	public InfinitNumber getEpsilon() {
		return mEpsilon;
	}

	/**
	 * Create a new linear arithmetic interpolator for an LA lemma.
	 *
	 * @param interpolator
	 *            the global interpolator.
	 * @param laLemma
	 *            the lemma that is interpolated.
	 */
	public LAInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
		mInterpolants = new Interpolant[mInterpolator.mNumInterpolants];
		for (int i = 0; i < mInterpolator.mNumInterpolants; i++) {
			mInterpolants[i] = new Interpolant();
		}
	}

	/**
	 * Interpolate an LA lemma. Normally, the interpolant is computed by summing up the A-part of all literals minding
	 * the Farkas coefficients. For trichotomy clauses we have to return the special trichotomy interpolant,
	 *
	 * <pre>
	 * LA(x1 + x2 &lt= 0, 0, x1 + x2 &lt= 0 and
	 *         (x1 + x2 &lt 0 or EQ(x, x1)))
	 * </pre>
	 *
	 * in the mixed case.
	 *
	 * @param lemma
	 *            the LA lemma that is interpolated.
	 */
	private void interpolateLemma(final Term lemma) {
		final InterpolatorAffineTerm[] ipl = new InterpolatorAffineTerm[mInterpolator.mNumInterpolants + 1];
		for (int part = 0; part < ipl.length; part++) {
			ipl[part] = new InterpolatorAffineTerm();
		}
		@SuppressWarnings("unchecked")
		final ArrayList<TermVariable>[] auxVars = new ArrayList[mInterpolator.mNumInterpolants];
		/*
		 * these variables are used for trichotomy clauses. The inequalityInfo will remember the information for one of
		 * the inequalities to get the aux literal. The equality will remember the equality literal (AnnotatedTerm), the
		 * eqApp the equality (ApplicationTerm), and equalityInfo will remember its info.
		 */
		Term equality = null;
		Term eqApp = null;
		LitInfo equalityInfo = null;
		Interpolator.Occurrence inequalityInfo = null;

		/*
		 * Add the A-part of the literals in this LA lemma.
		 */
		mLemmaInfo = mInterpolator.getClauseTermInfo(lemma);

		for (final Entry<Term, Rational> entry : mLemmaInfo.getFarkasCoeffs().entrySet()) {
			final Term lit = mInterpolator.mTheory.not(entry.getKey());
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(lit);
			final Rational factor = entry.getValue();
			if (litTermInfo.isBoundConstraint() || !litTermInfo.isNegated() && litTermInfo.isLAEquality()) {
				InfinitNumber bound;
				InterpolatorAffineTerm lv;
				if (litTermInfo.isBoundConstraint()) {
					assert factor.signum() == (litTermInfo.isNegated() ? -1 : 1);
					bound = new InfinitNumber(litTermInfo.getBound(), 0);
					// adapt the bound value for strict inequalities
					if (litTermInfo.isStrict()) {
						bound = bound.sub(litTermInfo.getEpsilon());
					}
					// get the inverse bound for negated literals
					if (litTermInfo.isNegated()) {
						bound = bound.add(litTermInfo.getEpsilon());
					}
					lv = litTermInfo.getLinVar();
				} else {
					assert litTermInfo.isLAEquality();
					lv = litTermInfo.getLinVar();
					bound = new InfinitNumber(litTermInfo.getBound(), 0);
				}
				final LitInfo info = mInterpolator.getLiteralInfo(litTermInfo.getAtom());
				inequalityInfo = info;

				int part = info.mInB.nextClearBit(0);
				while (part < ipl.length) {
					if (info.isMixed(part)) {
						/* ab-mixed interpolation */
						assert info.mMixedVar != null;
						ipl[part].add(factor, info.getAPart(part));
						ipl[part].add(factor.negate(), info.mMixedVar);

						if (auxVars[part] == null) {
							auxVars[part] = new ArrayList<>();
						}
						auxVars[part].add(info.mMixedVar);
					}
					if (info.isALocal(part)) {
						/* Literal in A: add to sum */
						ipl[part].add(factor, lv);
						ipl[part].add(bound.negate().mul(factor));
					}
					part++;
				}
			} else if (litTermInfo.isNegated() && litTermInfo.isLAEquality()) {
				// we have a Trichotomy Clause
				equality = litTermInfo.getAtom();
				// a trichotomy clause must contain exactly three parts
				assert mLemmaInfo.getLiterals().size() == 3;// NOCHECKSTYLE
				assert equalityInfo == null;
				equalityInfo = mInterpolator.getLiteralInfo(equality);
				eqApp = mInterpolator.unquote(equality);
				assert eqApp instanceof ApplicationTerm;
				assert factor.abs() == Rational.ONE;

				int part = equalityInfo.mInB.nextClearBit(0);
				while (part < ipl.length) {
					if (equalityInfo.isALocal(part)) {
						/* Literal in A: add epsilon to sum */
						ipl[part].add(litTermInfo.getEpsilon());
					}
					part++;
				}
			} else {
				assert false;
			}
		}
		assert ipl[ipl.length - 1].isConstant() && InfinitNumber.ZERO.less(ipl[ipl.length - 1].getConstant());

		/*
		 * Save the interpolants computed for this leaf into the result array.
		 */
		for (int part = 0; part < auxVars.length; part++) {
			final Rational normFactor = ipl[part].isConstant() ? Rational.ONE : ipl[part].getGCD().inverse().abs();
			ipl[part].mul(normFactor);
			/*
			 * Round up the (negated) constant if all terms in the interpolant are known to be integer. This is sound
			 * since x <= 0 is equivalent to ceil(x) <= 0.
			 */
			if (ipl[part].isInt()) {
				ipl[part].mConstant = ipl[part].getConstant().ceil();
			}

			if (auxVars[part] != null) { // NOPMD
				/*
				 * This is a mixed interpolant with auxiliary variables. Prepare an LATerm that wraps the interpolant.
				 */
				InfinitNumber k;
				Term F;
				if (equalityInfo != null) { // NOPMD
					/*
					 * This is a mixed trichotomy clause. This requires a very special interpolant.
					 */
					assert equalityInfo.isMixed(part);
					assert auxVars[part].size() == 2;
					assert normFactor == Rational.ONE;
					final InterpolatorAffineTerm less =
							new InterpolatorAffineTerm(ipl[part]).add(InfinitNumber.EPSILON);
					k = InfinitNumber.ZERO;
					F = mInterpolator.mTheory.and(ipl[part].toLeq0(mInterpolator.mTheory), mInterpolator.mTheory.or(
							less.toLeq0(mInterpolator.mTheory),
							mInterpolator.mTheory.equals(equalityInfo.getMixedVar(), auxVars[part].iterator().next())));
				} else {
					/* Just the inequalities are mixed. */
					if (ipl[part].isInt()) {
						k = InfinitNumber.ONE.negate();
					} else {
						k = InfinitNumber.EPSILON.negate();
					}
					F = ipl[part].toLeq0(mInterpolator.mTheory);
				}
				final LATerm laTerm = new LATerm(ipl[part], k, F);
				mInterpolants[part].mTerm = laTerm;
			} else {
				assert equalityInfo == null || !equalityInfo.isMixed(part);
				if (equalityInfo != null && ipl[part].isConstant()
						&& equalityInfo.isALocal(part) != inequalityInfo.isALocal(part)) {
					/*
					 * special case: Nelson-Oppen conflict, a <= b and b <= a in one partition, a != b in the other. If
					 * a != b is in A, the interpolant is simply a != b. If a != b is in B, the interpolant is simply a
					 * == b.
					 */
					final Term thisIpl = equalityInfo.isALocal(part) ? mInterpolator.mTheory.not(eqApp) : eqApp;
					mInterpolants[part].mTerm = thisIpl;
				} else {
					mInterpolants[part].mTerm = ipl[part].toLeq0(mInterpolator.mTheory);
				}
			}
		}
	}

	/**
	 * Computes partial interpolants for the LA lemma.
	 *
	 * @return an array containing the partial tree interpolants.
	 */
	public Interpolant[] computeInterpolants(final Term lemma) {
		interpolateLemma(lemma);
		return mInterpolants;
	}
}
