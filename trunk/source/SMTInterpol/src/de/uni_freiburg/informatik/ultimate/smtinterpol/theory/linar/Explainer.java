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
import java.util.Map;

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
	private final LinArSolve mSolver;
	/**
	 * Mapping of explained reason to annotation.  The form is such that the
	 * disjunction of the explained reason and the literals in the annotation
	 * form a lemma.
	 */
	private final Map<LAReason, LAAnnotation> mSubReasons;
	/**
	 * The unit literal that should be explained.  It is used to avoid using
	 * literals in the conflict that were only propagated after the literal
	 * to be explained was propagated.
	 */
	private final Literal mExplainedLiteral;

	/**
	 * The stack of reasons/annotations we are currently explaining. 
	 */
	private final ArrayDeque<LAAnnotation> mAnnotationStack;
	
	
	public Explainer(LinArSolve solver, boolean generateProofTree, 
			Literal explainedLiteral) {
		mSolver = solver;
		mExplainedLiteral = explainedLiteral;
		mSubReasons = new HashMap<LAReason, LAAnnotation>();
		mAnnotationStack = new ArrayDeque<LAAnnotation>();
		mAnnotationStack.add(new LAAnnotation());
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
		final DPLLAtom atom = lit.getAtom();
		return atom.getStackPosition() >= 0
			&& (mExplainedLiteral == null
			   || mExplainedLiteral.getAtom().getStackPosition() == -1
			   || atom.getStackPosition()
			< mExplainedLiteral.getAtom().getStackPosition());
	}

	/**
	 * Add a sub-annotation to the current LAAnnotation and explain it.
	 * @param reason The reason for which a sub-annotation is created.
	 * @param coeff The Farkas coefficient of the sub-annotation.
	 */
	public void addAnnotation(LAReason reason, Rational coeff) {
		assert ((coeff.signum() > 0) == reason.isUpper());
		final Rational sign = Rational.valueOf(coeff.signum(), 1);
		LAAnnotation annot = mSubReasons.get(reason);
		if (annot == null) {
			annot = new LAAnnotation(reason);
			mSubReasons.put(reason, annot);
			if (mAnnotationStack != null) {
				mAnnotationStack.addLast(annot);
			}
			reason.explain(this, reason.getVar().getEpsilon(), 
					sign);
			if (mAnnotationStack != null) {
				mAnnotationStack.removeLast();
			}
		}
		if (mAnnotationStack != null) {
			mAnnotationStack.getLast().addFarkas(annot, coeff);
		}
	}

	public void addEQAnnotation(LiteralReason reason, Rational coeff) {
		// FIXME: make a special annotation for disequalities
		assert ((coeff.signum() > 0) == reason.isUpper());
		final Rational sign = Rational.valueOf(coeff.signum(), 1); 
		LAAnnotation annot = mSubReasons.get(reason);
		if (annot == null) {
			annot = new LAAnnotation(reason);
			mSubReasons.put(reason, annot);
			mAnnotationStack.addLast(annot);
			if (reason.getOldReason() instanceof LiteralReason) {
				reason.getOldReason().explain(this, reason.getVar().getEpsilon(), sign);
			} else {
				addAnnotation(reason.getOldReason(), sign);
			}
			addLiteral(reason.getLiteral().negate(), sign);
			mAnnotationStack.removeLast();
		}
		mAnnotationStack.getLast().addFarkas(annot, coeff);
	}

	public void addLiteral(Literal lit, Rational coeff) {
		if (mAnnotationStack != null) {
			mAnnotationStack.getLast().addFarkas(lit, coeff);
		}
	}
	
	private boolean validClause() {
		if (mAnnotationStack == null) {
			return true;
		}
		assert (mAnnotationStack.size() == 1);
		MutableAffinTerm mat = mAnnotationStack.getFirst().addLiterals();
		assert (mat.isConstant() && InfinitNumber.ZERO.less(mat.getConstant()));
		for (final Map.Entry<LAReason, LAAnnotation> reasonEntry
			: mSubReasons.entrySet()) {
			final LAReason reason = reasonEntry.getKey();
			mat = reasonEntry.getValue().addLiterals();
			final Rational coeff = reason.isUpper() ? Rational.MONE : Rational.ONE;
			mat.add(coeff, reason.getVar());
			mat.add(reason.getBound().mul(coeff.negate()));
			mat.add(reason.getVar().getEpsilon());
			assert (mat.isConstant() && InfinitNumber.ZERO.less(mat.getConstant()));
		}
		return true;
	}
	
	public Clause createClause(DPLLEngine engine) {
		assert (mAnnotationStack.size() == 1);
		final LAAnnotation baseAnnotation = mAnnotationStack.getLast();
		final Literal[] lits = baseAnnotation.collectLiterals();
		final Clause clause = new Clause(lits);
		if (engine.isProofGenerationEnabled()) {
			clause.setProof(new LeafNode(
					LeafNode.THEORY_LA, baseAnnotation));
		}
		assert validClause();
		return clause;
	}

	/**
	 * Get the decide level on which all literals must live if they are
	 * allowed to appear in the explained clause. 
	 * @return the decide level of the explained unit literal or the current
	 * decide level if a conflict is explained.
	 */
	public int getDecideLevel() {
		return mExplainedLiteral == null 
				? mSolver.mEngine.getDecideLevel()
				: mExplainedLiteral.getAtom().getDecideLevel();
	}

	public Literal createComposite(CompositeReason reason) {
		return mSolver.createCompositeLiteral(reason, mExplainedLiteral);
	}
}
