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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;

/**
 * Annotation for a linear arithmetic conflict clause. It stores for every
 * reason literal a coefficient which can be used during interpolation.
 * 
 * For integer arithmetic we may have needed branches to derive this literal,
 * e.g., for Gomery cuts, or implicitly.  In that case we have an auxAnnotation
 * that is again explained by an annotation.
 * 
 * @author Juergen Christ, Jochen Hoenicke
 */
public class LAAnnotation implements IAnnotation {
	private static final Annotation g_trichotomy =
			new Annotation(":trichotomy", null);
	private LAAnnotation m_parent;
	/**
	 * Mapping of explained reason to annotation.  The form is such that the
	 * disjunction of the explained reason and the literals in the annotation
	 * form a lemma.
	 */
	private Map<LAReason, LAAnnotation> m_subReasons;
	/**
	 * Map from literal in the clause to a coefficient.
	 */
	private Map<Literal, Rational> m_coefficients;
	private Map<LAAnnotation, Rational> m_auxAnnotations;
	/**
	 * All literals in the clause.
	 */
	private Set<Literal> m_allLiterals;
	private Literal m_explainedLiteral;

	public LAAnnotation(boolean generateProofTree, Literal explainedLiteral) {
		generateProofTree = true; // TODO: hack
		if (generateProofTree) {
			m_coefficients   = new HashMap<Literal, Rational>();
			m_auxAnnotations = new HashMap<LAAnnotation, Rational>();
		}
		m_subReasons = new HashMap<LAReason, LAAnnotation>();
		m_allLiterals = new HashSet<Literal>();
		m_explainedLiteral = explainedLiteral;
		m_parent = this;
	}
	
	private LAAnnotation(LAAnnotation parent) {
		if (parent.m_coefficients != null) {
			m_coefficients   = new HashMap<Literal, Rational>();
			m_auxAnnotations = new HashMap<LAAnnotation, Rational>();
		}
		m_explainedLiteral = parent.m_explainedLiteral;
		m_parent = parent;
	}
	
	/**
	 * Returns the literal for which we generate a unit clause.  This is null
	 * if we generate a conflict clause.
	 * @return the explained literal.
	 */
	public Literal getExplainedLiteral() {
		return m_explainedLiteral;
	}
	
	public Map<Literal, Rational> getCoefficients() {
		return m_coefficients;
	}

	public Map<LAAnnotation, Rational> getAuxAnnotations() {
		return m_auxAnnotations;
	}

	public Map<LAReason, LAAnnotation> getSubReasons() {
		return m_subReasons;
	}

	public LAAnnotation addAnnotation(LAReason reason, Rational coeff, 
									  LinArSolve solver) {
		Rational sign = reason.isUpper() ? Rational.ONE : Rational.MONE;
		coeff = coeff.mul(sign);
		assert (coeff.signum() > 0);
		LAAnnotation annot = m_parent.m_subReasons.get(reason);
		if (annot != null) {
			if (m_coefficients != null) {
				Rational r = m_auxAnnotations.get(annot);
				if (r == null)
					r = Rational.ZERO;
				assert(r.signum() * coeff.signum() >= 0);
				r = r.add(coeff);
				m_auxAnnotations.put(annot, r);
			}
			return annot;
		}
		annot = new LAAnnotation(m_parent);
		m_parent.m_subReasons.put(reason, annot);
		if (m_coefficients != null)
			m_auxAnnotations.put(annot, coeff);
		reason.explain(annot, reason.getVar().getEpsilon(), 
					   sign, solver);
		return annot;
	}

	public LAAnnotation addEQAnnotation(LiteralReason reason, Rational coeff, 
			LinArSolve solver) {
		// FIXME: make a special annotation for disequalities
		Rational sign = reason.isUpper() ? Rational.ONE : Rational.MONE;
		coeff = coeff.mul(sign);
		assert (coeff.signum() > 0);
		LAAnnotation annot = m_parent.m_subReasons.get(reason);
		if (annot != null) {
			if (m_coefficients != null) {
				Rational r = m_auxAnnotations.get(annot);
				if (r == null)
					r = Rational.ZERO;
				assert(r.signum() * coeff.signum() >= 0);
				r = r.add(coeff);
				m_auxAnnotations.put(annot, r);
			}
			return annot;
		}
		annot = new LAAnnotation(m_parent);
		m_parent.m_subReasons.put(reason, annot);
		if (m_coefficients != null)
			m_auxAnnotations.put(annot, coeff);
		if (reason.getOldReason() instanceof LiteralReason) 
			reason.getOldReason().explain(annot, reason.getVar().getEpsilon(), sign, solver);
		else
			annot.addAnnotation(reason.getOldReason(), sign, solver);
		annot.addLiteral(reason.getLiteral().negate(), sign);
		return annot;
	}

	public void addLiteral(Literal lit, Rational coeff) {
		if (m_coefficients != null) {
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
		assert(!m_parent.m_allLiterals.contains(lit.negate()));
		m_parent.m_allLiterals.add(lit);
	}
	
	public Set<Literal> getLiterals() {
		return m_parent.m_allLiterals;
	}
	
	private MutableAffinTerm addLiterals() {
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
			LAReason reason = null;
			for (Map.Entry<LAReason, LAAnnotation> reasonEntry : 
				m_parent.m_subReasons.entrySet()) {
				if (reasonEntry.getValue() == annot) {
					reason = reasonEntry.getKey();
					break;
				}
			}
			assert (coeff.signum() > 0);
			if (!reason.isUpper())
				coeff = coeff.negate();
			mat.add(coeff, reason.getVar());
			mat.add(reason.getBound().mul(coeff.negate()));
		}
		return mat;
	}
	
	private boolean validClause() {
		if (m_coefficients == null)
			return true;
		MutableAffinTerm mat = addLiterals();
		assert (mat.isConstant() && InfinitNumber.ZERO.less(mat.getConstant()));
		for (Map.Entry<LAReason, LAAnnotation> reasonEntry : 
			m_subReasons.entrySet()) {
			LAReason reason = reasonEntry.getKey();
			mat = reasonEntry.getValue().addLiterals();
			Rational coeff = reason.isUpper() ? Rational.MONE : Rational.ONE;
			mat.add(coeff, reason.getVar());
			mat.add(reason.getBound().mul(coeff.negate()));
			mat.add(reason.getVar().getEpsilon());
			assert (mat.isConstant() && InfinitNumber.ZERO.less(mat.getConstant()));
		}
		return true;
	}
	
	public Clause createClause(DPLLEngine engine) {
		Literal[] lits = m_parent.m_allLiterals.toArray(new Literal[m_allLiterals.size()]);
		Clause clause = new Clause(lits);
		if (engine.isProofGenerationEnabled()) {
			clause.setProof(new LeafNode(LeafNode.THEORY_LA, this));
		}
		assert(m_parent == this);
		assert(validClause());
		return clause;
	}

	public String toString() {
		if (m_coefficients != null)
			return m_coefficients.toString() + m_auxAnnotations.toString();
		else
			return m_allLiterals.toString();
	}

	public boolean canExplainWith(BoundConstraint atom) {
		return atom.getStackPosition() > 0
			&& (m_explainedLiteral == null
			   || atom.getStackPosition() < 
			m_explainedLiteral.getAtom().getStackPosition());
	}

	@Override
	public String toSExpr(Theory smtTheory) {
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		if (m_coefficients != null) {
			sb.append(":farkas (");
			// TODO What is in the map? Looks like the conflict clause literals
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
		} else {
			sb.append(":litsum (");
			for (Literal lit : m_allLiterals)
				sb.append(lit.getSMTFormula(smtTheory));
			sb.append(')');
		}
		sb.append(')');
		return sb.toString();
	}
	
	@Override
	public Term toTerm(Clause ignored, Theory theory) {
		assert(m_coefficients != null);
		Map<LAAnnotation, Term> cache = new HashMap<LAAnnotation, Term>();
		Map<LAAnnotation, Term> expcache = new HashMap<LAAnnotation, Term>();
		if (m_parent.m_subReasons != null)
			for (Map.Entry<LAReason, LAAnnotation> me :
				m_parent.m_subReasons.entrySet()) {
				Term explained = me.getKey().toSMTLIB(theory, false);
				expcache.put(me.getValue(), explained);
			}
		ArrayDeque<LAAnnotation> todo = new ArrayDeque<LAAnnotation>();
		assert this == m_parent;
		todo.add(this);
		ArrayList<Term> antes = new ArrayList<Term>();
		todo_loop: while (!todo.isEmpty()) {
			LAAnnotation convert = todo.pop();
			Term res = cache.get(convert);
			if (res != null) {
				antes.add(res);
				continue;
			}
			int numdisjs = convert.m_coefficients.size() +
					convert.m_auxAnnotations.size();
			int i = 0;
			Term explained = expcache.get(convert);
			if (explained != null)
				++numdisjs;
			Term[] disjs = new Term[numdisjs];
			Term[] coeffs = new Term[numdisjs];
			Iterator<Rational> it = convert.m_coefficients.values().iterator();
			Rational gcd = null;
			if (it.hasNext())
				gcd = it.next();
			while (it.hasNext())
				gcd = gcd.gcd(it.next());
			it = convert.m_auxAnnotations.values().iterator();
			if (gcd == null && it.hasNext())
				gcd = it.next();
			while (it.hasNext())
				gcd = gcd.gcd(it.next());
			assert gcd != null;
			if (explained != null) {
				disjs[i] = explained;
				coeffs[i] = Rational.MONE.div(gcd).toSMTLIB(theory);
				++i;
			}
			boolean trichotomy = false;
			for (Map.Entry<Literal, Rational> me :
				convert.m_coefficients.entrySet()) {
				Literal lit = me.getKey();
				if (lit instanceof LAEquality)
					trichotomy = true;
				disjs[i] = me.getKey().getSMTFormula(theory);
				coeffs[i] = me.getValue().div(gcd).toSMTLIB(theory);
				++i;
			}
			for (Map.Entry<LAAnnotation, Rational> me :
				convert.m_auxAnnotations.entrySet()) {
				todo.push(me.getKey());
				Term expl = expcache.get(me.getKey());
				if (disjs.length == 2 && expl == disjs[0])
					continue todo_loop;
				disjs[i] = theory.term(theory.m_Not, expl);
				coeffs[i] = me.getValue().div(gcd).toSMTLIB(theory);
				++i;
			}
			res = theory.term(theory.m_Or, disjs);
			Annotation[] annots = new Annotation[] {
					trichotomy ? g_trichotomy :
							new Annotation(":LA", coeffs)
			};
			res = theory.annotatedTerm(annots, res);
			res = theory.term("@lemma", res);
			if (explained != null && !antes.isEmpty())
				res = theory.annotatedTerm(new Annotation[]{
				new Annotation(":pivot", explained)
				}, res);
			cache.put(convert, res);
			antes.add(res);
		}
		if (antes.size() == 1)
			return antes.get(0);
		return theory.term("@res", antes.toArray(new Term[antes.size()]));
	}
	
	public int hashCode() {//FIXME This hashCode is way too expensive
		return m_coefficients == null ? m_allLiterals.hashCode() :
			m_coefficients.hashCode();
	}
}
