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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Class used to annotate the input formulas such that interpolation is able to
 * discover the origin of a clause.
 *
 * @author Juergen Christ
 */
public class SourceAnnotation implements IAnnotation {
	public static final SourceAnnotation EMPTY_SOURCE_ANNOT = new SourceAnnotation("", null);
	private final String mAnnot;
	private final Term mProof;
	private final boolean mFromQuantTheory;

	public SourceAnnotation(final String annot, final Term proof) {
		mAnnot = annot;
		mProof = proof;
		mFromQuantTheory = false;
	}

	public SourceAnnotation(final SourceAnnotation orig, final boolean fromQuantTheory) {
		mAnnot = orig.mAnnot;
		mProof = orig.mProof;
		mFromQuantTheory = fromQuantTheory;
	}

	public SourceAnnotation(final SourceAnnotation orig, final Term newProof) {
		mAnnot = orig.mAnnot;
		mProof = newProof;
		mFromQuantTheory = orig.mFromQuantTheory;
	}

	public String getAnnotation() {
		return mAnnot;
	}

	public Term getSource() {
		return mProof;
	}

	public boolean isFromQuantTheory() {
		return mFromQuantTheory;
	}

	@Override
	public String toString() {
		return mAnnot;
	}

	@Override
	public Term toTerm(final Clause cls, final ProofRules proofRules) {
		final ProofLiteral[] proofLits = cls.toProofLiterals(proofRules);
		if (mProof == null) {
			// For partial proofs, make an oracle sub proof.
			final Annotation[] annots = new Annotation[] {
					new Annotation(ProofConstants.ANNOTKEY_INPUTCLAUSE, mAnnot.isEmpty() ? null : mAnnot) };
			return proofRules.oracle(proofLits, annots);
		} else {
			// Return the proof term annotated with input formula and proof literals
			final Annotation[] annots = new Annotation[] {
					new Annotation(ProofConstants.ANNOTKEY_PROVES,
							ProofRules.convertProofLiteralsToAnnotation(proofLits)),
					new Annotation(ProofConstants.ANNOTKEY_INPUTCLAUSE, mAnnot.isEmpty() ? null : mAnnot) };
			return mProof.getTheory().annotatedTerm(annots, mProof);
		}
	}
}
