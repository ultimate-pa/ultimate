/*
 * Copyright (C) 2019 University of Freiburg
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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * Class to interpolate Nelson-Oppen Theory combination lemmas. These lemmas propagate a CC equality to a LA equality or
 * vice versa.
 *
 * @author hoenicke
 *
 */
public class EQInterpolator {
	Interpolator mInterpolator;

	public EQInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
	}

	/**
	 * Convert this term to an InterpolatorAffineTerm
	 */
	static InterpolatorAffineTerm termToAffine(Term term) {
		if (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm) term).getSubterm();
		}
		final SMTAffineTerm affine = new SMTAffineTerm(term);
		return new InterpolatorAffineTerm(affine);
	}

	/**
	 * Compute the LA factor for this EQ lemma. This is the factor f, such that
	 * <code>f * (ccEq.getLhs() - ccEq.getRhs()) == laEq.getLhs())</code>
	 */
	private Rational getLAFactor(final InterpolatorAtomInfo ccEq, final InterpolatorAtomInfo laEq) {
		final SMTAffineTerm ccAffine = new SMTAffineTerm(ccEq.getEquality().getParameters()[0]);
		ccAffine.add(Rational.MONE, ccEq.getEquality().getParameters()[1]);
		assert !ccAffine.isConstant();
		final Map.Entry<Term, Rational> firstEntry = ccAffine.getSummands().entrySet().iterator().next();
		final Rational ccCoeff = firstEntry.getValue();
		final Rational laCoeff = laEq.getAffineTerm().getSummands().get(firstEntry.getKey());
		assert laCoeff != null && laCoeff != Rational.ZERO;
		return laCoeff.div(ccCoeff);
	}

	/**
	 * Compute the interpolants for a Nelson-Oppen equality clause. This is a theory lemma of the form equality implies
	 * equality, where one equality is congruence closure and one is linear arithmetic.
	 *
	 * @param trivialDiseq
	 *            the trivial disequality (a CC atom of the form s+k*a = s+k*b + k2.
	 * @param laEq
	 *            the linear arithmetic equality atom
	 * @param sign
	 *            the sign of l1 in the conflict clause. This is -1 if l1 implies l2, and +1 if l2 implies l1.
	 */
	public Term[] computeInterpolantsTrivialEq(Term trivialDiseq) {
		assert mInterpolator.isNegatedTerm(trivialDiseq);
		final Term equality = mInterpolator.getAtom(trivialDiseq);
		assert ((ApplicationTerm) equality).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Term[] eqParams = ((ApplicationTerm) equality).getParameters();
		final LitInfo ccOccInfo = mInterpolator.getAtomOccurenceInfo(equality);

		final Term[] interpolants = new Term[mInterpolator.mNumInterpolants];
		Rational factorK = null;
		for (int p = 0; p < mInterpolator.mNumInterpolants; p++) {
			Term interpolant;
			if (ccOccInfo.isAorShared(p)) {
				interpolant = mInterpolator.mTheory.mFalse; // literal in A.
			} else if (ccOccInfo.isBorShared(p)) {
				interpolant = mInterpolator.mTheory.mTrue; // literal in B.
			} else {
				// literal is mixed
				if (factorK == null) {
					// compute the factor of a/b if not already done.
					final SMTAffineTerm affine = new SMTAffineTerm();
					affine.add(Rational.ONE, eqParams[0]);
					affine.add(Rational.MONE, eqParams[1]);
					factorK = affine.getGcd();
					assert !affine.getConstant().div(factorK).isIntegral();
				}
				final SMTAffineTerm side = new SMTAffineTerm();
				side.add(Rational.ONE, ccOccInfo.mLhsOccur.isALocal(p) ? eqParams[0] : eqParams[1]);
				final SMTAffineTerm shared = new SMTAffineTerm();
				for (final Map.Entry<Term, Rational> entry : side.getSummands().entrySet()) {
					if (!entry.getValue().div(factorK).isIntegral()) {
						shared.add(entry.getValue(), entry.getKey());
					}
				}
				shared.add(side.getConstant());
				shared.add(Rational.MONE, ccOccInfo.getMixedVar());
				final Sort sort = eqParams[0].getSort();
				final Theory theory = mInterpolator.mTheory;
				interpolant = theory.term(SMTLIBConstants.EQUALS, theory.term("mod", shared.toTerm(sort), factorK.toTerm(sort)),
						Rational.ZERO.toTerm(sort));
			}
			interpolants[p] = interpolant;
		}
		return interpolants;
	}

	/**
	 * Compute the interpolants for a Nelson-Oppen equality clause. This is a theory
	 * lemma of the form equality implies equality, where one equality is congruence
	 * closure and one is linear arithmetic.
	 *
	 * @param ccEq the congruence closure equality atom
	 * @param laEq the linear arithmetic equality atom
	 * @param sign the sign of l1 in the conflict clause. This is -1 if l1 implies
	 *             l2, and +1 if l2 implies l1.
	 */
	public Term[] computeInterpolants(InterpolatorClauseInfo lemmaTermInfo) {
		Term[] interpolants = null;

		final Term[] eqParams = lemmaTermInfo.getLiterals();
		assert eqParams.length <= 2;
		if (eqParams.length == 1) {
			return computeInterpolantsTrivialEq(eqParams[0]);
		}
		final Term atom0 = mInterpolator.getAtom(eqParams[0]);
		final Term atom1 = mInterpolator.getAtom(eqParams[1]);
		final InterpolatorAtomInfo termInfo0 = mInterpolator.getAtomTermInfo(atom0);
		final InterpolatorAtomInfo termInfo1 = mInterpolator.getAtomTermInfo(atom1);
		assert mInterpolator.isNegatedTerm(eqParams[0]) != mInterpolator.isNegatedTerm(eqParams[1]);
		final LitInfo ccOccInfo, laOccInfo;
		final InterpolatorAtomInfo ccTermInfo, laTermInfo;
		final boolean ccIsNeg;
		if (termInfo0.isLAEquality()) {
			laTermInfo = termInfo0;
			ccTermInfo = termInfo1;
			laOccInfo = mInterpolator.getAtomOccurenceInfo(atom0);
			ccOccInfo = mInterpolator.getAtomOccurenceInfo(atom1);
			ccIsNeg = atom1 != eqParams[1];
		} else {
			laTermInfo = termInfo1;
			ccTermInfo = termInfo0;
			laOccInfo = mInterpolator.getAtomOccurenceInfo(atom1);
			ccOccInfo = mInterpolator.getAtomOccurenceInfo(atom0);
			ccIsNeg = atom0 != eqParams[0];
		}
		assert laTermInfo.isLAEquality() && ccTermInfo.isCCEquality();
		final Rational laFactor = getLAFactor(ccTermInfo, laTermInfo);

		interpolants = new Term[mInterpolator.mNumInterpolants];
		for (int p = 0; p < mInterpolator.mNumInterpolants; p++) {
			Term interpolant;
			if (ccOccInfo.isAorShared(p) && laOccInfo.isAorShared(p)) {
				interpolant = mInterpolator.mTheory.mFalse; // both literals in A.
			} else if (ccOccInfo.isBorShared(p) && laOccInfo.isBorShared(p)) {
				interpolant = mInterpolator.mTheory.mTrue; // both literals in B.
			} else {
				final InterpolatorAffineTerm iat = new InterpolatorAffineTerm();
				TermVariable mixed = null;
				boolean aPartNegated = false;
				// Get A part of ccEq:
				final ApplicationTerm ccEqApp = ccTermInfo.getEquality();
				if (ccOccInfo.isALocal(p)) {
					iat.add(laFactor, termToAffine(ccEqApp.getParameters()[0]));
					iat.add(laFactor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					if (!ccIsNeg) {
						aPartNegated = true;
					}
				} else if (ccOccInfo.isMixed(p)) {
					// mixed;
					if (!ccIsNeg) {
						mixed = ccOccInfo.getMixedVar();
					}
					if (ccOccInfo.mLhsOccur.isALocal(p)) {
						iat.add(laFactor, termToAffine(ccEqApp.getParameters()[0]));
						iat.add(laFactor.negate(), ccOccInfo.getMixedVar());
					} else {
						iat.add(laFactor, ccOccInfo.getMixedVar());
						iat.add(laFactor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					}
				} else {
					// both sides in B, A part is empty
				}

				// Get A part of laEq:
				if (laOccInfo.isALocal(p)) {
					iat.add(Rational.MONE, laTermInfo.getAffineTerm());
					if (ccIsNeg) {
						aPartNegated = true;
					}
				} else if (laOccInfo.isMixed(p)) {
					if (ccIsNeg) {
						mixed = laOccInfo.getMixedVar();
					}
					iat.add(Rational.MONE, laOccInfo.getAPart(p));
					iat.add(Rational.ONE, laOccInfo.getMixedVar());
				} else {
					// both sides in B, A part is empty
				}
				iat.mul(iat.getGcd().inverse());

				// Now solve it.
				if (mixed != null) { // NOPMD
					final Rational mixedFactor = iat.getSummands().remove(mixed);
					assert mixedFactor.isIntegral();
					final boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) { // NOPMD
						if (mixedFactor.signum() > 0) {
							iat.negate();
						}
						final Term sharedTerm = iat.toSMTLib(mInterpolator.mTheory, isInt);
						final Term divisor = mixedFactor.abs().toTerm(mixed.getSort());
						// We need to divide sharedTerm by mixedFactor and check that it doesn't produce a remainder.
						//
						// Interpolant is: (and (= mixed (div sharedTerm mixedFactor))
						// (= (mod sharedTerm mixedFactor) 0))
						interpolant = mInterpolator.mTheory.and(
								mInterpolator.mTheory.term(Interpolator.EQ, mixed,
										mInterpolator.mTheory.term("div", sharedTerm, divisor)),
								mInterpolator.mTheory.term("=", mInterpolator.mTheory.term("mod", sharedTerm, divisor),
										Rational.ZERO.toTerm(mixed.getSort())));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						final Term sharedTerm = iat.toSMTLib(mInterpolator.mTheory, isInt);
						interpolant = mInterpolator.mTheory.term(Interpolator.EQ, mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitesimalNumber.ZERO) {
							aPartNegated ^= true;
						}
						interpolant = aPartNegated ? mInterpolator.mTheory.mFalse : mInterpolator.mTheory.mTrue;
					} else {
						final boolean isInt = iat.isInt();
						final Sort sort = mInterpolator.mTheory.getSort(isInt ? "Int" : "Real");
						final Term term = iat.toSMTLib(mInterpolator.mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						interpolant = aPartNegated ? mInterpolator.mTheory.not(mInterpolator.mTheory.equals(term, zero))
								: mInterpolator.mTheory.equals(term, zero);
					}
				}
			}
			interpolants[p] = interpolant;
		}
		return interpolants;
	}
}
