/*
 * Copyright (C) 2009-2013 University of Freiburg
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;

/**
 * This class is used to explain a conflict clause found by the LA solver.
 * When proofs are generated, this class builds the corresponding LAAnnotation.
 * It also determines which literals are necessary to occur in the conflict
 * clause.
 * 
 * @author Jochen Hoenicke
 */
public class Explainer {
	/**
	 * The linear arithmetic solver.  This is used to create new composite
	 * literals.
	 */
	private LinArSolve m_solver;
	/**
	 * Mapping of explained reason to annotation.  The form is such that the
	 * disjunction of the explained reason and the literals in the annotation
	 * form a lemma.
	 */
	private Map<LAReason, LAAnnotation> m_subReasons;
	/**
	 * All literals in the conflict clause.
	 */
	private Set<Literal> m_allLiterals;
	/**
	 * The unit literal that should be explained.  It is used to avoid using
	 * literals in the conflict that were only propagated after the literal
	 * to be explained was propagated.
	 */
	private Literal m_explainedLiteral;

	/**
	 * The stack of reasons/annotations we are currently explaining. 
	 */
	private ArrayDeque<LAAnnotation> m_annotationStack;
	
	
	public Explainer(LinArSolve solver, boolean generateProofTree, 
			Literal explainedLiteral) {
		m_solver = solver;
		m_allLiterals = new HashSet<Literal>();
		m_explainedLiteral = explainedLiteral;
		m_subReasons = new HashMap<LAReason, LAAnnotation>();
		if (generateProofTree) {
			m_annotationStack = new ArrayDeque<LAAnnotation>();
			m_annotationStack.add(new LAAnnotation());
		}
	}

	/**
	 * Check if the literal can be used to explain this clause.  It checks
	 * it against the unit literal that should be explained by a unit clause.
	 * If the given literal "lit" has a lower stack position than the unit 
	 * literal for which the unit clause is generated, it may not be used in 
	 * the explanation.
	 * @param lit The literal that we would like to include in the 
	 *             explanation clause.
	 * @return true if the literal may appear in the clause.
	 */
	public boolean canExplainWith(Literal lit) {
		DPLLAtom atom = lit.getAtom();
		return atom.getStackPosition() >= 0
			&& (m_explainedLiteral == null
			   || m_explainedLiteral.getAtom().getStackPosition() == -1
			   || atom.getStackPosition() < 
			m_explainedLiteral.getAtom().getStackPosition());
	}

	/**
	 * Add a sub-annotation to the current LAAnnotation and explain it.
	 * @param reason The reason for which a sub-annotation is created.
	 * @param coeff The Farkas coefficient of the sub-annotation.
	 */
	public void addAnnotation(LAReason reason, Rational coeff) {
		assert ((coeff.signum() > 0) == reason.isUpper());
		Rational sign = Rational.valueOf(coeff.signum(), 1);
		LAAnnotation annot = m_subReasons.get(reason);
		if (annot == null) {
			annot = new LAAnnotation(reason);
			m_subReasons.put(reason, annot);
			if (m_annotationStack != null)
				m_annotationStack.addLast(annot);
			reason.explain(this, reason.getVar().getEpsilon(), 
					sign);
			if (m_annotationStack != null)
				m_annotationStack.removeLast();
		}
		if (m_annotationStack != null)
			m_annotationStack.getLast().addFarkas(annot, coeff);
	}

	public void addEQAnnotation(LiteralReason reason, Rational coeff) {
		// FIXME: make a special annotation for disequalities
		assert ((coeff.signum() > 0) == reason.isUpper());
		Rational sign = Rational.valueOf(coeff.signum(), 1); 
		LAAnnotation annot = m_subReasons.get(reason);
		if (annot == null) {
			annot = new LAAnnotation(reason);
			m_subReasons.put(reason, annot);
			if (m_annotationStack != null)
				m_annotationStack.addLast(annot);
			if (reason.getOldReason() instanceof LiteralReason) 
				reason.getOldReason().explain(this, reason.getVar().getEpsilon(), sign);
			else
				addAnnotation(reason.getOldReason(), sign);
			addLiteral(reason.getLiteral().negate(), sign);
			if (m_annotationStack != null)
				m_annotationStack.removeLast();
		}
		if (m_annotationStack != null)
			m_annotationStack.getLast().addFarkas(annot, coeff);
	}

	public void addLiteral(Literal lit, Rational coeff) {
		if (m_annotationStack != null) {
			m_annotationStack.getLast().addFarkas(lit, coeff);
		}
		// sanity check: a literal should never appear in both polarities
		assert(!m_allLiterals.contains(lit.negate()));
		m_allLiterals.add(lit);
	}
	
	private boolean validClause() {
		if (m_annotationStack == null)
			return true;
		assert (m_annotationStack.size() == 1);
		MutableAffinTerm mat = m_annotationStack.getFirst().addLiterals();
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
		Literal[] lits = m_allLiterals.toArray(new Literal[m_allLiterals.size()]);
		Clause clause = new Clause(lits);
		if (engine.isProofGenerationEnabled()) {
			assert (m_annotationStack.size() == 1);
			clause.setProof(new LeafNode(LeafNode.THEORY_LA, m_annotationStack.getFirst()));
		}
		assert(validClause());
		return clause;
	}

	/**
	 * Get the decide level on which all literals must live if they are
	 * allowed to appear in the explained clause. 
	 * @return the decide level of the explained unit literal or the current
	 * decide level if a conflict is explained.
	 */
	public int getDecideLevel() {
		return m_explainedLiteral == null 
				? m_solver.mengine.getDecideLevel()
				: m_explainedLiteral.getAtom().getDecideLevel();
	}

	public Literal createComposite(CompositeReason reason) {
		return m_solver.createCompositeLiteral(reason, m_explainedLiteral);
	}
}
