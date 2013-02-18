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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAReason;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class LAInterpolator {

	Interpolator m_Interpolator;
	LAAnnotation m_Annotation;

	HashMap<LAAnnotation, LAReason> subAnnotToReason;
	
	HashMap<LAAnnotation, AnnotInfo> m_AuxInfos 
	= new HashMap<LAAnnotation, AnnotInfo>();

	class AnnotInfo extends Interpolator.Occurrence {
		LAAnnotation m_myAnnotation;
		
		private MutableAffinTerm m_Sum;		
		Interpolant[] m_Interpolants;

		InterpolatorAffineTerm m_mixedSums[];
		TermVariable m_AuxVar;
		InfinitNumber m_Epsilon;
		
		public AnnotInfo(LAAnnotation auxAnnot) {
			m_Interpolator.super();
			m_myAnnotation = auxAnnot;
			//we only need sum and stuff for subannotations
			if(!auxAnnot.equals(m_Annotation)) { 
				computeSum();
				color();
				computeMixedSums();
			}
		}
		
		void computeSum() {
			LAReason reason = subAnnotToReason.get(m_myAnnotation);
			m_Sum = new MutableAffinTerm();
			m_Sum.add(reason.isUpper() ? Rational.ONE : Rational.MONE, reason.getVar());
			m_Sum.add(reason.isUpper() ? reason.getBound().negate() : reason.getBound());
			m_Epsilon = reason.getVar().getEpsilon();
		}
		private void color() {
			boolean isFirst = true;
			for (LinVar lv : m_Sum.getSummands().keySet()) {
				Interpolator.Occurrence occ = 
						m_Interpolator.m_SymbolPartition.get(lv.getSharedTerm());
				assert (occ != null);
				if (isFirst) {
					m_inA.or(occ.m_inA);
					m_inB.or(occ.m_inB);
					isFirst = false;
				} else {
					m_inA.and(occ.m_inA);
					m_inB.and(occ.m_inB);
				}
			}
		}

		private void computeMixedSums() {
			BitSet shared = new BitSet();
			shared.or(m_inA);
			shared.or(m_inB);
			if (shared.nextClearBit(0) == m_Interpolator.m_NumInterpolants)
				return;
			
			m_mixedSums = new InterpolatorAffineTerm[m_Interpolator.m_NumInterpolants];
			m_AuxVar = 
				m_Interpolator.m_Theory.createFreshTermVariable("msaux", 
						m_Sum.getSort(m_Interpolator.m_Theory));

			for (int part = 0; part < m_Interpolator.m_NumInterpolants; part++) {
				if (isMixed(part)) {
					InterpolatorAffineTerm sumApart = new InterpolatorAffineTerm();

					LAReason reason = subAnnotToReason.get(m_myAnnotation);
					LinVar lv = reason.getVar();

					for(Entry<LinVar, BigInteger> en : lv.getLinTerm().entrySet()) {
						Occurrence occ = 
							m_Interpolator.m_SymbolPartition.get(
									en.getKey().getSharedTerm());

						if (occ.isALocal(part)) {
							Rational coeff = 
								Rational.valueOf(en.getValue(), BigInteger.ONE);
							sumApart.add(coeff, en.getKey());
						}
					}
					sumApart.add(Rational.MONE, m_AuxVar); 
				
					if (!reason.isUpper())
						sumApart.negate();

					m_mixedSums[part] = sumApart;
				}
			}
		}
		
		/**
		 * @return
		 */
		private MutableAffinTerm getSum() {
			return m_Sum;
			
		}
		
		InterpolatorAffineTerm getMixedSum(int part) {
			return m_mixedSums[part];
		}

		public InfinitNumber getEpsilon() {
			return m_Epsilon;
		}
	}

	public LAInterpolator(Interpolator interpolator,
			LAAnnotation theoryAnnotation) {
		m_Interpolator = interpolator;
		m_Annotation = theoryAnnotation;
		
		subAnnotToReason = new HashMap<LAAnnotation, LAReason>();
		for (Entry<LAReason, LAAnnotation> en : 
			m_Annotation.getSubReasons().entrySet()) 
			subAnnotToReason.put(en.getValue(), en.getKey());
		
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
		AnnotInfo result = m_AuxInfos.get(auxAnnot);
		if (result != null)
			return result;
		
		result = new AnnotInfo(auxAnnot);
		result.m_Interpolants = new Interpolant[m_Interpolator.m_NumInterpolants];
		for (int i = 0; i < m_Interpolator.m_NumInterpolants; i++)
			result.m_Interpolants[i] = new Interpolant();
 
		for (LAAnnotation annot : auxAnnot.getAuxAnnotations().keySet())
			computeAuxAnnotations(annot); 
		interpolateLeaf(auxAnnot, result);
		interpolateInnerNode(auxAnnot, result);

		m_AuxInfos.put(auxAnnot, result);		
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
		InterpolatorAffineTerm[] ipl = new InterpolatorAffineTerm[m_Interpolator.m_NumInterpolants+1];
		for (int part = 0; part < ipl.length; part++)
			ipl[part] = new InterpolatorAffineTerm();
		@SuppressWarnings("unchecked")
		ArrayList<TermVariable>[] auxVars = 
			new ArrayList[m_Interpolator.m_NumInterpolants];
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
		if(auxAnnot != m_Annotation) {
			// Sum A parts of negated auxAnnot.
			int part = result.m_inB.nextClearBit(0);
			while (part < ipl.length) {
				if (result.isMixed(part)) {
					ipl[part].add(Rational.MONE, result.getMixedSum(part));
					if (auxVars[part] == null)
						auxVars[part] = new ArrayList<TermVariable>();
					auxVars[part].add(result.m_AuxVar);
				}
				if (result.isALocal(part)) {
					ipl[part].add(Rational.MONE, result.getSum());
					ipl[part].add(result.getEpsilon());
				}	
				part++;
			}
		}
		/* Add the A-part of the summary for all used sub-annotations.
		 */
		for (Entry<LAAnnotation, Rational> entry : auxAnnot.getAuxAnnotations().entrySet()) {
			AnnotInfo info = m_AuxInfos.get(entry.getKey());
			Rational coeff = entry.getValue();
			// Sum A parts of info.
			int part = info.m_inB.nextClearBit(0);
			while (part < ipl.length) {
				if (info.isMixed(part)) {
					ipl[part].add(coeff, info.getMixedSum(part));
					if (auxVars[part] == null)
						auxVars[part] = new ArrayList<TermVariable>();
					auxVars[part].add(info.m_AuxVar);
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
				LitInfo info = m_Interpolator.getLiteralInfo(lit.getAtom());
				inequalityInfo = info;

				int part = info.m_inB.nextClearBit(0);
				while (part < ipl.length) {
					if (info.isMixed(part)) {
						/* ab-mixed interpolation */
						assert (info.m_MixedVar != null);
						ipl[part].add(factor, info.getAPart(part));
						ipl[part].add(factor.negate(), info.m_MixedVar);
	
						if (auxVars[part] == null)
							auxVars[part] = new ArrayList<TermVariable>();
						auxVars[part].add(info.m_MixedVar);
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
				    + (auxAnnot == m_Annotation ? 0 : 1) == 3;
				assert equalityInfo == null;
				equalityInfo = m_Interpolator.getLiteralInfo(eq);
				assert factor.abs() == Rational.ONE;

				int part = equalityInfo.m_inB.nextClearBit(0);
				while (part < ipl.length) {
					if (equalityInfo.isALocal(part)) {
						/* Literal in A: add epsilon to sum */
						ipl[part].add(eq.getVar().getEpsilon());
					}
					part++;
				}
			}
		}
		assert (ipl[ipl.length-1].isConstant() 
				&& InfinitNumber.ZERO.less(ipl[ipl.length-1].getConstant()));
		
		/*
		 * Save the interpolants computed for this leaf into the result array.
		 */
		for (int part = 0; part < auxVars.length; part++) {
			Rational normFactor = ipl[part].isConstant() ? Rational.ONE
					: ipl[part].getGCD().inverse().abs();
			ipl[part].mul(normFactor);
			if (auxVars[part] != null) {
				/* This is a mixed interpolant with auxiliary variables.
				 * Prepare an LAInfo that wraps the interpolant.
				 */
				TermVariable placeHolder = 
						m_Interpolator.m_Theory.createFreshTermVariable(
								"LA", m_Interpolator.m_Theory.getBooleanSort());
				InfinitNumber k;
				Term F;
				if (equalityInfo != null) {
					/* This is a mixed trichotomy class.  This requires a
					 * very special interpolant.
					 */
					assert equalityInfo.isMixed(part);
					assert auxVars[part].size() == 2;
					assert normFactor == Rational.ONE;
					InterpolatorAffineTerm less = 
						new InterpolatorAffineTerm(ipl[part]).add(InfinitNumber.EPSILON);
					k = InfinitNumber.ZERO;
					F = m_Interpolator.m_Theory.and(
							ipl[part].toLeq0(m_Interpolator.m_Theory),
							m_Interpolator.m_Theory.or(less.toLeq0(m_Interpolator.m_Theory),
							m_Interpolator.m_Theory.equals
							(equalityInfo.getMixedVar(), 
							 auxVars[part].iterator().next())));
				} else {
					if (ipl[part].isInt())
						k = InfinitNumber.ONE.negate();
					else
						k = InfinitNumber.EPSILON.negate();
					F = ipl[part].toLeq0(m_Interpolator.m_Theory);
				}
				LAInfo eqIn = new LAInfo(ipl[part], k, F);
				result.m_Interpolants[part].m_term = placeHolder;
				result.m_Interpolants[part].m_VarToLA.put(placeHolder, eqIn);
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
					result.m_Interpolants[part].m_term = 
						thisIpl.getSMTFormula(m_Interpolator.m_Theory);
				} else {
					result.m_Interpolants[part].m_term = 
						ipl[part].toLeq0(m_Interpolator.m_Theory);
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
			for (int part = 0; part < m_Interpolator.m_NumInterpolants; part++) {
				if (subInfo.isBLocal(part)) {
					/* Literal in B: and */
					result.m_Interpolants[part].m_term = m_Interpolator.m_Theory.
							and(result.m_Interpolants[part].m_term, subInfo.m_Interpolants[part].m_term);
					m_Interpolator.mergeLAHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				} else if (subInfo.isMixed(part)) {
					TermVariable mixedVar = subInfo.m_AuxVar;
					result.m_Interpolants[part] = m_Interpolator.mixedPivotLA(
							result.m_Interpolants[part], subInfo.m_Interpolants[part], mixedVar);
				} else if (subInfo.isAB(part)) {
					/* Literal is shared: ite */
					result.m_Interpolants[part].m_term = 
						m_Interpolator.m_Theory.ifthenelse
								(subInfo.getSum().toSMTLibLeq0(m_Interpolator.m_Theory, false), 
								result.m_Interpolants[part].m_term, 
								subInfo.m_Interpolants[part].m_term);
					m_Interpolator.mergeLAHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				} else {
					/* Literal in A: or */
					result.m_Interpolants[part].m_term = m_Interpolator.m_Theory.
							or(result.m_Interpolants[part].m_term, subInfo.m_Interpolants[part].m_term);
					m_Interpolator.mergeLAHashMaps(result.m_Interpolants[part], subInfo.m_Interpolants[part]);
				}
			}
		}
	}
	
	public Interpolant[] computeInterpolants() {
		AnnotInfo annotInfo = computeAuxAnnotations(m_Annotation);
		return annotInfo.m_Interpolants;
	}
}
