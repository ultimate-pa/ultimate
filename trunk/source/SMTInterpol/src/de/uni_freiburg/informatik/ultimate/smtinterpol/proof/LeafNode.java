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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Proof node representing a leaf in the proof tree. This might either be an
 * input clause or a theory lemma.
 * @author Juergen Christ
 */
public class LeafNode extends ProofNode {
	/// No theory created this node => input clause.
	public final static int NO_THEORY = -1;
	/// Quantifier Instantiation
	public final static int QUANT_INST = -2;
	/// EUF-lemma
	public final static int THEORY_CC = -3;
	/// LA(R/Z)-lemma
	public final static int THEORY_LA = -4;
	/// Array lemma
	public final static int THEORY_ARRAY = -5;
	/// NO equality propagation
	public final static int EQ = -6;
	/// An assumption
	public final static int ASSUMPTION = -7;

	private final int mLeafKind;
	private IAnnotation mAnnotation;
	
	public LeafNode(int leafKind, IAnnotation annot) {
		mLeafKind = leafKind;
		mAnnotation = annot;
	}
	
	@Override
	public boolean isLeaf() {
		return true;
	}
	/**
	 * Which theory created this leaf node.
	 * @return Identifier for the theory which created this leaf.
	 */
	public int getLeafKind() {
		return mLeafKind;
	}
	/**
	 * Is this the annotation for a tautology?
	 * @return <code>true</code> if this annotation represents a tautology.
	 */
	public boolean isTautology() {
		return mLeafKind >= 0;
	}
	/**
	 * Check if the leaf has a source annotation. This means it
	 * was created from a single input formula.
	 * @return <code>true</code> iff this leaf node has a source annotation.
	 */
	public boolean hasSourceAnnotation() {
		// Only source nodes and tautologies
		return mLeafKind >= NO_THEORY;
	}
	/**
	 * Get theory specific annotations.
	 * @return Theory specific annotations.
	 */
	public IAnnotation getTheoryAnnotation() {
		return mAnnotation;
	}
	/**
	 * Set theory specific annotations.
	 * @param annot New theory specific annotations.
	 */
	public void setTheoryAnnotation(IAnnotation annot) {
		mAnnotation = annot;
	}
	@Override
	public String toString() {
		return "[" + mAnnotation + "]";
	}
}
