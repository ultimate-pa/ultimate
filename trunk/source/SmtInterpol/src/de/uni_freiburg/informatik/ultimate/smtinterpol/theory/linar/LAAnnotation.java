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
	private Map<Literal, Rational> m_coefficients;
	/**
	 * Map from sub-annotations to a Farkas coefficient.  The sub-annotations
	 * must all have the same parent annotation as this annotation (and must
	 * be distinct from this annotation to avoid circular reasoning).  When 
	 * summing up the inequalities, the bound explained by the sub-annotation
	 * must be multiplied with the coefficient from this map.
	 */
	private Map<LAAnnotation, Rational> m_auxAnnotations;
	
	/**
	 * The linvar on which this sub-annotation explains a bound, or null
	 * if this is the top-most annotation.
	 * If this is a sub-annotation, it explains a bound on a linear variable.
	 */
	private LinVar m_linvar;
	/**
	 * The linvar on which this sub-annotation explains a bound, or null
	 * if this is the top-most annotation.
	 * If this is a sub-annotation, it explains a bound on a linear variable.
	 */
	private InfinitNumber m_bound;
	/**
	 * True, if this is a sub-annotation that explains an upper bound on a
	 * linear variable.
	 * If this is a sub-annotation, it explains a bound on a linear variable,
	 * either a lower or an upper bound.
	 */
	private boolean m_isUpper;

	public LAAnnotation() {
		m_coefficients   = new HashMap<Literal, Rational>();
		m_auxAnnotations = new HashMap<LAAnnotation, Rational>();
	}
	
	public LAAnnotation(LAReason reason) {
		this();
		m_linvar = reason.getVar();
		m_bound = reason.getBound();
		m_isUpper = reason.isUpper();
	}
	
	public Map<Literal, Rational> getCoefficients() {
		return m_coefficients;
	}

	public Map<LAAnnotation, Rational> getAuxAnnotations() {
		return m_auxAnnotations;
	}

	public void addFarkas(LAAnnotation annot, Rational coeff) { 
		Rational r = m_auxAnnotations.get(annot);
		if (r == null)
			r = Rational.ZERO;
		assert(r.signum() * coeff.signum() >= 0);
		r = r.add(coeff);
		m_auxAnnotations.put(annot, r);
	}

	public void addFarkas(Literal lit, Rational coeff) {
		Rational r = m_coefficients.get(lit);
		if (r == null)
			r = Rational.ZERO;
		assert(lit.getAtom() instanceof LAEquality
			   || r.signum() * coeff.signum() >= 0);
		r = r.add(coeff);
		if (r == Rational.ZERO)
			m_coefficients.remove(lit);
		else
			m_coefficients.put(lit, r);
	}
	
	MutableAffinTerm addLiterals() {
		MutableAffinTerm mat = new MutableAffinTerm();
		for (Map.Entry<Literal, Rational> entry : m_coefficients.entrySet()) {
			Rational coeff = entry.getValue(); 
			Literal lit = entry.getKey();
			if (lit.getAtom() instanceof BoundConstraint) {
				BoundConstraint bc = (BoundConstraint) lit.getAtom();
				InfinitNumber bound = bc.getBound();
				assert ((coeff.signum() > 0) == (bc != lit));
				if (bc == lit) {
					bound = bc.getInverseBound();
				}
				mat.add(coeff, bc.getVar());
				mat.add(bound.mul(coeff.negate()));
			} else {
				LAEquality lasd = (LAEquality) lit.getAtom();
				if (lasd != lit) {
					mat.add(coeff, lasd.getVar());
					mat.add(lasd.getBound().mul(coeff.negate()));
				} else {
					assert coeff.abs().equals(Rational.ONE);
					// TODO check that matching inequality is present.
					mat.add(lasd.getVar().getEpsilon());
				}
			}
		}
		for (Map.Entry<LAAnnotation, Rational> entry : m_auxAnnotations.entrySet()) {
			Rational coeff = entry.getValue(); 
			LAAnnotation annot = entry.getKey();
			assert ((coeff.signum() > 0) == annot.m_isUpper);
			mat.add(coeff, annot.m_linvar);
			mat.add(annot.m_bound.mul(coeff.negate()));
		}
		return mat;
	}
	
	public String toString() {
		return m_coefficients.toString() + m_auxAnnotations.toString();
	}

	@Override
	public String toSExpr(Theory smtTheory) {
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		sb.append(":farkas (");
		for (Map.Entry<Literal, Rational> me : m_coefficients.entrySet()) {
			sb.append("(* ").append(me.getValue().toString()).append(' ');
			sb.append(me.getKey().negate().getSMTFormula(smtTheory)).append(')');
		}
		sb.append(')');
		if (m_auxAnnotations != null && !m_auxAnnotations.isEmpty()) {
			for (Map.Entry<LAAnnotation, Rational> me : m_auxAnnotations.entrySet()) {
				sb.append(" (:subproof (* ").append(me.getValue().toString());
				sb.append(' ').append(me.getKey().toSExpr(smtTheory));
				sb.append("))");
			}
		}
		sb.append(')');
		return sb.toString();
	}
	
	@Override
	public Term toTerm(Clause ignored, Theory theory) {
		assert(m_coefficients != null);
		return new AnnotationToProofTerm().convert(this, theory);
	}
	
	public int hashCode() {
		return m_linvar == null ? 0 : 
			HashUtils.hashJenkins(m_bound.hashCode(), m_linvar);
	}
	
	public LinVar getLinVar() {
		return m_linvar;
	}
	
	public InfinitNumber getBound() {
		return m_bound;
	}
	
	public boolean isUpper() {
		return m_isUpper;
	}
}
