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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.BoundConstraint;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class LAInterpolator {

	Interpolator mInterpolator;
	LAAnnotation mAnnotation;

	HashMap<LAAnnotation, AnnotInfo> mAuxInfos 
	    = new HashMap<LAAnnotation, AnnotInfo>();

	class AnnotInfo extends Interpolator.Occurrence {
		LAAnnotation mMyAnnotation;
		
		private MutableAffinTerm mSum;		
		Interpolant[] mInterpolants;

		InterpolatorAffineTerm[] mMixedSums;
		TermVariable mAuxVar;
		InfinitNumber mEpsilon;
		
		public AnnotInfo(LAAnnotation auxAnnot) {
			mInterpolator.super();
			mMyAnnotation = auxAnnot;
			//we only need sum and stuff for subannotations
			if (!auxAnnot.equals(mAnnotation)) { 
				computeSum();
				color();
				computeMixedSums();
			}
		}
		
		private void computeSum() {
			mSum = new MutableAffinTerm();
			mSum.add(Rational.ONE, mMyAnnotation.getLinVar());
			mSum.add(mMyAnnotation.getBound().negate());
			mEpsilon = mMyAnnotation.getLinVar().getEpsilon();
		}
		private void color() {
			boolean isFirst = true;
			for (LinVar lv : mSum.getSummands().keySet()) {
				Interpolator.Occurrence occ = 
						mInterpolator.mSymbolPartition.get(lv.getSharedTerm());
				assert (occ != null);
				if (isFirst) {
					mInA.or(occ.mInA);
					mInB.or(occ.mInB);
					isFirst = false;
				} else {
					mInA.and(occ.mInA);
					mInB.and(occ.mInB);
				}
			}
		}

		private void computeMixedSums() {
			BitSet shared = new BitSet();
			shared.or(mInA);
			shared.or(mInB);
			if (shared.nextClearBit(0) == mInterpolator.mNumInterpolants)
				return;
			
			mMixedSums = new InterpolatorAffineTerm[mInterpolator.mNumInterpolants];
			mAuxVar = 
				mInterpolator.mTheory.createFreshTermVariable("msaux", 
						mSum.getSort(mInterpolator.mTheory));

			for (int part = 0; part < mInterpolator.mNumInterpolants; part++) {
				if (isMixed(part)) {
					InterpolatorAffineTerm sumApart = new InterpolatorAffineTerm();

					LinVar lv = mMyAnnotation.getLinVar();

					for (Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
						Occurrence occ = 
							mInterpolator.mSymbolPartition.get(
									en.getKey().getSharedTerm());

						if (occ.isALocal(part)) {
							Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
							sumApart.add(coeff, en.getKey());
						}
					}
					sumApart.add(Rational.MONE, mAuxVar); 
				
					mMixedSums[part] = sumApart;
				}
			}
		}
		
		/**
		 * @return
		 */
		private MutableAffinTerm getSum() {
			return mSum;
			
		}
		
		InterpolatorAffineTerm getMixedSum(int part) {
			return mMixedSums[part];
		}

		public InfinitNumber getEpsilon() {
			return mEpsilon;
		}
	}

	public LAInterpolator(Interpolator interpolator,
			LAAnnotation theoryAnnotation) {
		mInterpolator = interpolator;
		mAnnotation = theoryAnnotation;
	}

	/**
	 * Compute the summary, aux variable and interpolants for a annotation
	 * or sub-annotation.  This function caches the information, so that
	 * it is only computed once.
	 * @param auxAnnot The annotation of which the information should be
	 * 	computed.
	 * @return An AnnotInfo containing all the information.
	 */
	private AnnotInfo computeAuxAnnotations(LAAnnotation auxAnnot) {
		AnnotInfo result = mAuxInfos.get(auxAnnot);
		if (result != null)
			return result;
		
		result = new AnnotInfo(auxAnnot);
		result.mInterpolants = new Interpolant[mInterpolator.mNumInterpolants];
		for (int i = 0; i < mInterpolator.mNumInterpolants; i++)
			result.mInterpolants[i] = new Interpolant();
 
		for (LAAnnotation annot : auxAnnot.getAuxAnnotations().keySet())
			computeAuxAnnotations(annot); 
		interpolateLeaf(auxAnnot, result);
		interpolateInnerNode(auxAnnot, result);

		mAuxInfos.put(auxAnnot, result);		
		return result;
	}


	/**
	 * Interpolate a leaf node that explains the sub-proof auxAnnot.
	 * This sub-proof explains how the normalized and rounded summary of
	 * auxAnnot is implied by its literals and sub-annotations.  Note that
	 * this is not an interpolant of the sub annotation, since it does
	 * not yet contain the interpolant for its own sub-annotations.
	 * You have to call interpolateInnerNode afterwards.
	 * 
	 * The interpolant is computed by summing up the A-part of all
	 * sub-annotations, literals, and the negated summary of this annotation. 
	 * @param auxAnnot the sub-proof that is interpolated.
	 * @param result the normalized and rounded summary of auxAnnot.
	 */
	private void interpolateLeaf(LAAnnotation auxAnnot, AnnotInfo result) {
		InterpolatorAffineTerm[] ipl =
		        new InterpolatorAffineTerm[mInterpolator.mNumInterpolants + 1];
		for (int part = 0; part < ipl.length; part++)
			ipl[part] = new InterpolatorAffineTerm();
		@SuppressWarnings("unchecked")
		ArrayList<TermVariable>[] auxVars = 
			new ArrayList[mInterpolator.mNumInterpolants];
		/* these variables are used for trichotomy clauses.
		 * The inequalityInfo will remember the information for
		 * one of the inequalities to get the aux literal.
		 * The equality will remember the equality literal and 
		 * equalityInfo will remember its info.
		 */
		Literal equality = null;
		LitInfo equalityInfo = null;
		Interpolator.Occurrence inequalityInfo = null;
		/* if this leaf is a sub-annotation, i.e. we have to add the
		 * negated summary to get a conflict clause. 
		 * 
		 * To compute the interpolant we have to add the A-part
		 * of the negated summary.
		 */
		if (auxAnnot != mAnnotation) {
			// Sum A parts of negated auxAnnot.
			int part = result.mInB.nextClearBit(0);
			while (part < ipl.length) {
				Rational coeff = auxAnnot.isUpper() ? Rational.MONE : Rational.ONE;
				if (result.isMixed(part)) {
					ipl[part].add(coeff, result.getMixedSum(part));
					if (auxVars[part] == null)
						auxVars[part] = new ArrayList<TermVariable>();
					auxVars[part].add(result.mAuxVar);
				}
				if (result.isALocal(part)) {
					ipl[part].add(coeff, result.getSum());
					ipl[part].add(result.getEpsilon());
				}	
				part++;
			}
		}
		/* Add the A-part of the summary for all used sub-annotations.
		 */
		for (Entry<LAAnnotation, Rational> entry : auxAnnot.getAuxAnnotations().entrySet()) {
			AnnotInfo info = mAuxInfos.get(entry.getKey());
			Rational coeff = entry.getValue();
			// Sum A parts of info.
			int part = info.mInB.nextClearBit(0);
			while (part < ipl.length) {
				if (info.isMixed(part)) {
					ipl[part].add(coeff, info.getMixedSum(part));
					if (auxVars[part] == null)
						auxVars[part] = new ArrayList<TermVariable>();
					auxVars[part].add(info.mAuxVar);
				}
				if (info.isALocal(part)) {
					ipl[part].add(coeff, info.getSum());
				}
				part++;
			}
			inequalityInfo = info;
		}
		
		/* Add the A-part of the literals in this annotation.
		 */
		for (Entry<Literal, Rational> entry : auxAnnot.getCoefficients().entrySet()) {
			
			Literal lit = entry.getKey().negate();
			Rational factor = entry.getValue();
			if (lit.getAtom() instanceof BoundConstraint || lit instanceof LAEquality) {
				InfinitNumber bound;
				LinVar lv;
				if (lit.getAtom() instanceof BoundConstraint) {
					assert factor.signum() == lit.getSign();
					BoundConstraint bc = (BoundConstraint) lit.getAtom();
					bound =	lit.getSign() > 0 ? bc.getBound() : bc.getInverseBound();
					lv = bc.getVar();
				} else  {
					assert lit instanceof LAEquality;
					LAEquality eq = (LAEquality) lit;
					lv = eq.getVar();
					bound = new InfinitNumber(eq.getBound(), 0);
				}
				LitInfo info = mInterpolator.getLiteralInfo(lit.getAtom());
				inequalityInfo = info;

				int part = info.mInB.nextClearBit(0);
				while (part < ipl.length) {
					if (info.isMixed(part)) {
						/* ab-mixed interpolation */
						assert (info.mMixedVar != null);
						ipl[part].add(factor, info.getAPart(part));
						ipl[part].add(factor.negate(), info.mMixedVar);
	
						if (auxVars[part] == null)
							auxVars[part] = new ArrayList<TermVariable>();
						auxVars[part].add(info.mMixedVar);
					}
					if (info.isALocal(part)) {
						/* Literal in A: add to sum */
						ipl[part].add(factor, lv);
						ipl[part].add(bound.negate().mul(factor));
					}
					part++;
				}
			} else if (lit.negate() instanceof LAEquality) {
				//we have a Trichotomy Clause
				equality = lit.negate();
				LAEquality eq = (LAEquality) equality;
				//a trichotomy clause must contain exactly three parts
				assert auxAnnot.getAuxAnnotations().size() + auxAnnot.getCoefficients().size()
				    + (auxAnnot == mAnnotation ? 0 : 1) == 3;// NOCHECKSTYLE
				assert equalityInfo == null;
				equalityInfo = mInterpolator.getLiteralInfo(eq);
				assert factor.abs() == Rational.ONE;

				int part = equalityInfo.mInB.nextClearBit(0);
				while (part < ipl.length) {
					if (equalityInfo.isALocal(part)) {
						/* Literal in A: add epsilon to sum */
						ipl[part].add(eq.getVar().getEpsilon());
					}
					part++;
				}
			}
		}
		assert (ipl[ipl.length - 1].isConstant() 
				&& InfinitNumber.ZERO.less(ipl[ipl.length - 1].getConstant()));
		
		/*
		 * Save the interpolants computed for this leaf into the result array.
		 */
		for (int part = 0; part < auxVars.length; part++) {
			Rational normFactor = ipl[part].isConstant() ? Rational.ONE
					: ipl[part].getGCD().inverse().abs();
			ipl[part].mul(normFactor);
			if (auxVars[part] != null) { // NOPMD
				/* This is a mixed interpolant with auxiliary variables.
				 * Prepare an LATerm that wraps the interpolant.
				 */
				InfinitNumber k;
				Term F;
				if (equalityInfo != null) { // NOPMD
					/* This is a mixed trichotomy class.  This requires a
					 * very special interpolant.
					 */
					assert equalityInfo.isMixed(part);
					assert auxVars[part].size() == 2;
					assert normFactor == Rational.ONE;
					InterpolatorAffineTerm less = 
						new InterpolatorAffineTerm(ipl[part]).add(
						        InfinitNumber.EPSILON);
					k = InfinitNumber.ZERO;
					F = mInterpolator.mTheory.and(
							ipl[part].toLeq0(mInterpolator.mTheory),
							mInterpolator.mTheory.or(less.toLeq0(mInterpolator.mTheory),
							        mInterpolator.mTheory.equals(
							                equalityInfo.getMixedVar(), 
							                auxVars[part].iterator().next())));
				} else {
					if (ipl[part].isInt())
						k = InfinitNumber.ONE.negate();
					else
						k = InfinitNumber.EPSILON.negate();
					F = ipl[part].toLeq0(mInterpolator.mTheory);
				}
				LATerm laTerm = new LATerm(ipl[part], k, F);
				result.mInterpolants[part].mTerm = laTerm;
			} else {
				assert (equalityInfo == null 
						|| !equalityInfo.isMixed(part));
				if (equalityInfo != null && ipl[part].isConstant()
					&& equalityInfo.isALocal(part) != inequalityInfo.isALocal(part)) {
					/* special case: Nelson-Oppen conflict, a < b and b < a in
					 * one partition, a != b in the other.
					 * If a != b is in A, the interpolant is simply a != b
					 * If a != b is in B, the interpolant is simply a == b
					 */
					Literal thisIpl = equalityInfo.isALocal(part) 
						? equality.negate() : equality;
					result.mInterpolants[part].mTerm = 
						thisIpl.getSMTFormula(mInterpolator.mTheory);
				} else {
					result.mInterpolants[part].mTerm = 
						ipl[part].toLeq0(mInterpolator.mTheory);
				}
			}
		}
	}

	/**
	 * This function computes the complete interpolant for an annotation 
	 * by resolving it with all interpolants of its sub-annotations.
	 *
	 * @param auxAnnot the annotation for which the interpolant should
	 * 	       be computed.
	 * @param result The info where the interpolants are stored.  On call
	 *         it must contain the interpolants computed by interpolateLeaf.
	 */
	private void interpolateInnerNode(LAAnnotation auxAnnot, AnnotInfo result) {
		for (Entry<LAAnnotation, Rational> auxAnn : auxAnnot.getAuxAnnotations().entrySet()) {
			LAAnnotation annot = auxAnn.getKey();
			AnnotInfo subInfo = computeAuxAnnotations(annot);
			for (int part = 0; part < mInterpolator.mNumInterpolants; part++) {
				if (subInfo.isBLocal(part)) {
					/* Literal in B: and */
					result.mInterpolants[part].mTerm = mInterpolator.mTheory.
							and(result.mInterpolants[part].mTerm,
							        subInfo.mInterpolants[part].mTerm);
				} else if (subInfo.isMixed(part)) {
					TermVariable mixedVar = subInfo.mAuxVar;
					result.mInterpolants[part] = mInterpolator.mixedPivotLA(
							result.mInterpolants[part],
							subInfo.mInterpolants[part], mixedVar);
				} else if (subInfo.isAB(part)) {
					/* Literal is shared: ite */
					MutableAffinTerm mat = new MutableAffinTerm();
					Rational coeff = annot.isUpper() ? Rational.ONE : Rational.MONE;
					mat.add(coeff, subInfo.getSum());
					result.mInterpolants[part].mTerm = 
						mInterpolator.mTheory.ifthenelse(
								mat.toSMTLibLeq0(mInterpolator.mTheory, false), 
								result.mInterpolants[part].mTerm, 
								subInfo.mInterpolants[part].mTerm);
				} else {
					/* Literal in A: or */
					result.mInterpolants[part].mTerm = mInterpolator.mTheory.
							or(result.mInterpolants[part].mTerm,
							        subInfo.mInterpolants[part].mTerm);
				}
			}
		}
	}
	
	public Interpolant[] computeInterpolants() {
		AnnotInfo annotInfo = computeAuxAnnotations(mAnnotation);
		return annotInfo.mInterpolants;
	}
}
