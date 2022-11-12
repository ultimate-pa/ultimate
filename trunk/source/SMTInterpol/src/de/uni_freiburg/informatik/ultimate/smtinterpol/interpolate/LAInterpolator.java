/*
 * Copyright (C) 2009-2019 University of Freiburg
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
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

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
	public final static String ANNOT_LA = ":LA";

	Interpolator mInterpolator;

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
	}

	/**
	 * Create an {@code LA(s,k,F)} term. This is now represented as an annotated term {@code (! F :LA (s k))}
	 *
	 * @param s
	 *            The affine term {@code s} with {@code s >= 0 ==> F}.
	 * @param k
	 *            The interval length {@code k} with {@code s + k < 0 ==> ~F}.
	 * @param formula
	 *            The formula F.
	 */
	public static Term createLATerm(final InterpolatorAffineTerm s, final InfinitesimalNumber k, final Term formula) {
		final Theory theory = formula.getTheory();
		return theory.annotatedTerm(new Annotation[] { new Annotation(ANNOT_LA, new Object[] { s, k }) }, formula);
	}

	/**
	 * Check if a term is an {@code LA(s,k,F)} term.
	 *
	 * @param term
	 *            The term to check.
	 * @return true if it is an LA term, false otherwise.
	 */
	public static boolean isLATerm(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final Annotation[] annot = ((AnnotatedTerm) term).getAnnotations();
			return annot.length == 1 && annot[0].getKey().equals(ANNOT_LA);
		}
		return false;
	}

	/**
	 * Get the s part of an {@code LA(s,k,F)} term. This assumes the term is an LA term.
	 *
	 * @param term
	 *            The LA term.
	 * @return the s part.
	 */
	public static InterpolatorAffineTerm getS(final Term term) {
		assert isLATerm(term);
		return (InterpolatorAffineTerm) ((Object[]) ((AnnotatedTerm) term).getAnnotations()[0].getValue())[0];
	}

	/**
	 * Get the k part of an {@code LA(s,k,F)} term. This assumes the term is an LA term.
	 *
	 * @param term
	 *            The LA term.
	 * @return the k part.
	 */
	public static InfinitesimalNumber getK(final Term term) {
		assert isLATerm(term);
		return (InfinitesimalNumber) ((Object[]) ((AnnotatedTerm) term).getAnnotations()[0].getValue())[1];
	}

	/**
	 * Get the F part of an {@code LA(s,k,F)} term. This assumes the term is an LA term.
	 *
	 * @param term
	 *            The LA term.
	 * @return the F part.
	 */
	public static Term getF(final Term term) {
		assert isLATerm(term);
		return ((AnnotatedTerm) term).getSubterm();
	}

	/**
	 * Compute the literals and corresponding Farkas coefficients for this LA lemma
	 */
	private HashMap<Term, Rational> getFarkasCoeffs(final InterpolatorClauseInfo clauseInfo) {
		final HashMap<Term, Rational> coeffMap = new HashMap<>();
		final Term[] lits = clauseInfo.getLiterals();
		final Object[] coeffs = (Object[]) clauseInfo.getLemmaAnnotation();
		for (int i = 0; i < coeffs.length; i++) {
			final Rational coeff = SMTAffineTerm.convertConstant((ConstantTerm) coeffs[i]);
			coeffMap.put(lits[i], coeff);
		}
		return coeffMap;
	}

	/**
	 * Interpolate an LA lemma. The interpolant is computed by summing up the A-part of all literals minding the Farkas
	 * coefficients.
	 *
	 * @param lemma
	 *            the LA lemma that is interpolated.
	 * @return an array containing the partial tree interpolants.
	 */
	public Term[] computeInterpolants(final InterpolatorClauseInfo lemmaInfo) {
		final InterpolatorAffineTerm[] ipl = new InterpolatorAffineTerm[mInterpolator.mNumInterpolants + 1];
		for (int part = 0; part < ipl.length; part++) {
			ipl[part] = new InterpolatorAffineTerm();
		}
		@SuppressWarnings("unchecked")
		final ArrayList<TermVariable>[] auxVars = new ArrayList[mInterpolator.mNumInterpolants];

		/*
		 * Add the A-part of the literals in this LA lemma.
		 */
		for (final Entry<Term, Rational> entry : getFarkasCoeffs(lemmaInfo).entrySet()) {
			final Term atom = mInterpolator.getAtom(entry.getKey());
			final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
			// Is the literal negated in conflict? I.e. not negated in clause.
			final boolean isNegated = atom == entry.getKey();
			final Rational factor = entry.getValue();
			assert atomTermInfo.isBoundConstraint() || (!isNegated && atomTermInfo.isLAEquality());
			final LitInfo occurrenceInfo = mInterpolator.getAtomOccurenceInfo(atom);

			final InterpolatorAffineTerm lv = new InterpolatorAffineTerm(atomTermInfo.getAffineTerm());
			/* for negated literals subtract epsilon because we need the inverse bound */
			if (isNegated) {
				lv.add(atomTermInfo.getEpsilon().negate());
			}
			for (int part = 0; part < ipl.length; part++) {
				if (occurrenceInfo.isMixed(part)) {
					/* ab-mixed interpolation */
					assert occurrenceInfo.mMixedVar != null;
					ipl[part].add(factor, occurrenceInfo.getAPart(part));
					ipl[part].add(factor.negate(), occurrenceInfo.mMixedVar);

					if (auxVars[part] == null) {
						auxVars[part] = new ArrayList<>();
					}
					auxVars[part].add(occurrenceInfo.mMixedVar);
				} else if (occurrenceInfo.isALocal(part)) {
					/* Literal in A: add to sum */
					ipl[part].add(factor, lv);
				}
			}
		}
		assert ipl[ipl.length - 1].isConstant() && ipl[ipl.length - 1].getConstant().signum() > 0;

		/*
		 * Save the interpolants computed for this leaf into the result array.
		 */
		final Term[] interpolants = new Term[mInterpolator.mNumInterpolants];
		for (int part = 0; part < auxVars.length; part++) {
			final Rational normFactor = ipl[part].isConstant() ? Rational.ONE : ipl[part].getGcd().inverse().abs();
			ipl[part].mul(normFactor);
			/*
			 * Round up the (negated) constant if all terms in the interpolant are known to be integer. This is sound
			 * since x <= 0 is equivalent to ceil(x) <= 0.
			 */
			if (ipl[part].isInt()) {
				final InfinitesimalNumber constant = ipl[part].getConstant();
				ipl[part].add(constant.ceil().sub(constant));
			}

			interpolants[part] = ipl[part].toLeq0(mInterpolator.mTheory);
			if (auxVars[part] != null) { // NOPMD
				/*
				 * This is a mixed interpolant with auxiliary variables. Prepare an LATerm that wraps the interpolant.
				 */
				final InfinitesimalNumber epsilon =
						ipl[part].isInt() ? InfinitesimalNumber.ONE : InfinitesimalNumber.EPSILON;
				interpolants[part] = createLATerm(ipl[part], epsilon.negate(), interpolants[part]);
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate an LA trichotomy. We have to return the special trichotomy interpolant,
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
	 * @return an array containing the partial tree interpolants.
	 */
	public Term[] computeTrichotomyInterpolants(final InterpolatorClauseInfo lemmaInfo) {
		// Count number of A-local and B-local literals and remember one of them.
		// Collect the occurence info for the equality and the mix var for inequality and negated inequality.
		LitInfo equalityOccurenceInfo = null;
		TermVariable ineqMix = null, negIneqMix = null;
		final int[] numALocal = new int[mInterpolator.mNumInterpolants];
		final int[] numBLocal = new int[mInterpolator.mNumInterpolants];
		final Term[] aLocalLit = new Term[mInterpolator.mNumInterpolants];
		final Term[] bLocalLit = new Term[mInterpolator.mNumInterpolants];

		assert lemmaInfo.getLiterals().length == 3;
		for (final Term lit : lemmaInfo.getLiterals()) {
			final Term atom = mInterpolator.getAtom(lit);
			final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
			final LitInfo occurrenceInfo = mInterpolator.getAtomOccurenceInfo(atom);
			// Is the literal negated in conflict?  I.e. not negated in clause.
			final boolean isNegated = atom == lit;
			for (int part = 0; part < mInterpolator.mNumInterpolants; part++) {
				if (occurrenceInfo.isALocal(part)) {
					numALocal[part]++;
					aLocalLit[part] = lit;
				} else if (occurrenceInfo.isBLocal(part)) {
					numBLocal[part]++;
					bLocalLit[part] = lit;
				}
			}
			if (atomTermInfo.isBoundConstraint()) {
				if (isNegated) {
					negIneqMix = occurrenceInfo.getMixedVar();
				} else {
					ineqMix = occurrenceInfo.getMixedVar();
				}
			} else {
				assert isNegated && atomTermInfo.isLAEquality();
				equalityOccurenceInfo = occurrenceInfo;
			}
		}

		// Compute the interpolants.
		final Term[] interpolants = new Term[mInterpolator.mNumInterpolants];
		for (int part = 0; part < mInterpolator.mNumInterpolants; part++) {
			if (equalityOccurenceInfo.isMixed(part)) {
				/*
				 * This is a mixed trichotomy clause. This requires a very special interpolant.
				 */
				final InterpolatorAffineTerm s = new InterpolatorAffineTerm();
				s.add(Rational.MONE, ineqMix);
				s.add(Rational.ONE, negIneqMix);
				final Term leqTerm = mInterpolator.mTheory.term("<=", negIneqMix, ineqMix);
				final Term lessTerm = mInterpolator.mTheory.term("<", negIneqMix, ineqMix);
				final Term F = mInterpolator.mTheory.and(leqTerm, mInterpolator.mTheory.or(lessTerm,
						mInterpolator.mTheory.term(Interpolator.EQ, equalityOccurenceInfo.getMixedVar(), ineqMix)));
				interpolants[part] = createLATerm(s, InfinitesimalNumber.ZERO, F);
			} else {
				assert numALocal[part] + numBLocal[part] <= 3;
				if (numALocal[part] == 0) {
					// all occurences in B
					interpolants[part] = mInterpolator.mTheory.mTrue;
				} else if (numBLocal[part] == 0) {
					// all occurences in A
					interpolants[part] = mInterpolator.mTheory.mFalse;
				} else if (numALocal[part] == 1) {
					/* summarize the A-local literal */
					interpolants[part] = mInterpolator.mTheory.not(aLocalLit[part]);
				} else {
					assert numBLocal[part] == 1;
					/* summarize the B-local literal */
					interpolants[part] = bLocalLit[part];
				}
			}
		}
		return interpolants;
	}
}
