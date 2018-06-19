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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Annotation for a linear arithmetic conflict.  This roughly stores the 
 * proof in form of Farkas coefficients for the base literals and 
 * sub-annotations.  The sub-annotations can be seen as auxiliary clauses
 * that handle extended branches, e.g., for Gomery cuts.
 * 
 * If m_linvar is null, this is a base annotation, which corresponds to a 
 * proof of unsatisfiability of the current conflict.  Otherwise it is a
 * sub-annotation corresponding to a proof for some bound on a variable, 
 * which is given by m_linvar, m_bound, and m_isUpper.  
 * 
 * An annotation is basically a sum of inequalities with Farkas coefficients.
 * An inequality can either be a literal in the current conflict, i.e., the
 * negation of a literal in the conflict clause, or it can be a LAReason that
 * is explained by some different sub-annotation.  The maps m_coefficients
 * and m_auxAnnotations map these inequalities to their respective Farkas
 * coefficient.  The literals in the coefficient map appear negated, i.e., in
 * the same polarity that they have in the conflict clause.  The sum of the 
 * inequalities must yield the explained LAReason for a sub-annotation (in the 
 * integer case some rounding may be involved), or an inconsistency (e.g., 
 * 1 <= 0) for the parent annotation.
 *
 * Instead of an inequality literals and sub-annotations, an annotation may 
 * also add equalities (which can be seen as a strengthened inequality).
 * 
 * There is a special type of annotations, a trichotomy, that involves a
 * disequality and two inequalities, namely, term !=0, term <= 0, term >= 0.
 * If it is a base annotation, it will contain these three literals in its
 * coefficient and auxAnnotation maps.  If it is a sub-annotation it must 
 * either explain term < 0 or term >0 from the literals term != 0 and term >=0
 * resp. term <=0.
 * 
 * 
 * @author Juergen Christ, Jochen Hoenicke
 */
public class LAAnnotation implements IAnnotation {
	/**
	 * Map from literal in the clause to a Farkas coefficient.  Note that
	 * the literal has the same polarity as in the clause.  When summing up
	 * the inequalities the literal must be negated first and then multiplied
	 * with the coefficient from this map.
	 */
	private final Map<Literal, Rational> mCoefficients;
	/**
	 * Map from sub-annotations to a Farkas coefficient.  The sub-annotations
	 * must all have the same parent annotation as this annotation (and must
	 * be distinct from this annotation to avoid circular reasoning).  When 
	 * summing up the inequalities, the bound explained by the sub-annotation
	 * must be multiplied with the coefficient from this map.
	 */
	private final Map<LAAnnotation, Rational> mAuxAnnotations;
	
	/**
	 * The linvar on which this sub-annotation explains a bound, or null
	 * if this is the top-most annotation.
	 * If this is a sub-annotation, it explains a bound on a linear variable.
	 */
	private LinVar mLinvar;
	/**
	 * The linvar on which this sub-annotation explains a bound, or null
	 * if this is the top-most annotation.
	 * If this is a sub-annotation, it explains a bound on a linear variable.
	 */
	private InfinitNumber mBound;
	/**
	 * True, if this is a sub-annotation that explains an upper bound on a
	 * linear variable.
	 * If this is a sub-annotation, it explains a bound on a linear variable,
	 * either a lower or an upper bound.
	 */
	private boolean mIsUpper;

	public LAAnnotation() {
		mCoefficients   = new HashMap<Literal, Rational>();
		mAuxAnnotations = new HashMap<LAAnnotation, Rational>();
	}
	
	public LAAnnotation(LAReason reason) {
		this();
		mLinvar = reason.getVar();
		mBound = reason.getBound();
		mIsUpper = reason.isUpper();
	}
	
	public Map<Literal, Rational> getCoefficients() {
		return mCoefficients;
	}

	public Map<LAAnnotation, Rational> getAuxAnnotations() {
		return mAuxAnnotations;
	}

	public void addFarkas(LAAnnotation annot, Rational coeff) { 
		Rational r = mAuxAnnotations.get(annot);
		if (r == null) {
			r = Rational.ZERO;
		}
		assert(r.signum() * coeff.signum() >= 0);
		r = r.add(coeff);
		mAuxAnnotations.put(annot, r);
	}

	public void addFarkas(Literal lit, Rational coeff) {
		Rational r = mCoefficients.get(lit);
		if (r == null) {
			r = Rational.ZERO;
		}
		assert lit.getAtom() instanceof LAEquality || r.signum() * coeff.signum() >= 0;
		r = r.add(coeff);
		if (r == Rational.ZERO) {
			mCoefficients.remove(lit);
		} else {
			mCoefficients.put(lit, r);
		}
	}
	
	MutableAffinTerm addLiterals() {
		final MutableAffinTerm mat = new MutableAffinTerm();
		for (final Map.Entry<Literal, Rational> entry : mCoefficients.entrySet()) {
			final Rational coeff = entry.getValue(); 
			final Literal lit = entry.getKey();
			if (lit.getAtom() instanceof BoundConstraint) {
				final BoundConstraint bc = (BoundConstraint) lit.getAtom();
				InfinitNumber bound = bc.getBound();
				assert ((coeff.signum() > 0) == (bc != lit));
				if (bc == lit) {
					bound = bc.getInverseBound();
				}
				mat.add(coeff, bc.getVar());
				mat.add(bound.mul(coeff.negate()));
			} else {
				final LAEquality lasd = (LAEquality) lit.getAtom();
				if (lasd == lit) {
					assert coeff.abs().equals(Rational.ONE);
					// TODO check that matching inequality is present.
					mat.add(lasd.getVar().getEpsilon());
				} else {
					mat.add(coeff, lasd.getVar());
					mat.add(lasd.getBound().mul(coeff.negate()));
				}
			}
		}
		for (final Map.Entry<LAAnnotation, Rational> entry : mAuxAnnotations.entrySet()) {
			final Rational coeff = entry.getValue(); 
			final LAAnnotation annot = entry.getKey();
			assert ((coeff.signum() > 0) == annot.mIsUpper);
			mat.add(coeff, annot.mLinvar);
			mat.add(annot.mBound.mul(coeff.negate()));
		}
		return mat;
	}
	
	@Override
	public String toString() {
		return mCoefficients.toString() + mAuxAnnotations.toString();
	}

	@Override
	public Term toTerm(Clause ignored, Theory theory) {
		assert(mCoefficients != null);
		return new AnnotationToProofTerm().convert(this, theory);
	}
	
	@Override
	public int hashCode() {
		return mLinvar == null ? 0 : HashUtils.hashJenkins(mBound.hashCode(), mLinvar);
	}
	
	public LinVar getLinVar() {
		return mLinvar;
	}
	
	public InfinitNumber getBound() {
		return mBound;
	}
	
	public boolean isUpper() {
		return mIsUpper;
	}
	
	private void collect(HashSet<Literal> lits, HashSet<LAAnnotation> visited) {
		if (visited.add(this)) {
			lits.addAll(mCoefficients.keySet());
			for (final LAAnnotation annot : mAuxAnnotations.keySet()) {
				annot.collect(lits, visited);
			}
		}
	}

	public Literal[] collectLiterals() {
		final HashSet<Literal> lits = new HashSet<Literal>();
		collect(lits, new HashSet<LAAnnotation>());
		return lits.toArray(new Literal[lits.size()]);
	}
}
