/*
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;

/**
 * This class is used to gather the information from a proof term which is
 * relevant for the interpolator.
 *
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class InterpolatorClauseInfo {
	enum ClauseKind {
		RESOLUTION, LEMMA, INPUT
	}

	/**
	 * The literals of this clause. This may be null for resolution clauses, if the literals haven't been computed yet.
	 * For leaf clauses this is always set correctly.
	 */
	private Term[] mLiterals;

	/**
	 * The type of this leaf term, i.e. lemma or clause
	 */
	private final ClauseKind mNodeKind;

	/**
	 * The arguments of this resolution term
	 */
	private Term[] mResolutionArgs;

	/**
	 * The lemma annotation, if this is a lemma leaf node.
	 */
	private Annotation mLemmaAnnotation;

	/**
	 * Create the information for a proof term representing a clause. This fills in all relevant fields for the given
	 * proof term.
	 */
	public InterpolatorClauseInfo(final Term term) {
		if (ProofRules.isProofRule(ProofRules.RES, term)) {
			mNodeKind = ClauseKind.RESOLUTION;
		} else {
			final AnnotatedTerm annotTerm = (AnnotatedTerm) term;
			mLemmaAnnotation = annotTerm.getAnnotations()[1];
			if (mLemmaAnnotation.getKey() == ProofConstants.ANNOTKEY_RUP) {
				mNodeKind = ClauseKind.RESOLUTION;
			} else if (mLemmaAnnotation.getKey() == ProofConstants.ANNOTKEY_INPUTCLAUSE) {
				mNodeKind = ClauseKind.INPUT;
			} else {
				mNodeKind = ClauseKind.LEMMA;
			}
			mLiterals = computeLiterals((Object[]) annotTerm.getAnnotations()[0].getValue());
		}
	}

	/**
	 * Fill in the field mLiterals for this resolution term only if needed (i.e. if deep check is switched on)
	 */
	public void computeResolutionLiterals(final Interpolator interpolator) {
		assert isResolution();
		final LinkedHashSet<Term> literals = new LinkedHashSet<>();
		final InterpolatorClauseInfo primInfo = interpolator.mClauseTermInfos.get(mResolutionArgs[1]);
		final Term pivot = mResolutionArgs[0];
		for (final Term primLit : primInfo.getLiterals()) {
			if (primLit != pivot) {
				literals.add(primLit);
			}
		}
		final InterpolatorClauseInfo antecedentInfo = interpolator.mClauseTermInfos.get(mResolutionArgs[2]);
		final Term negPivot = pivot.getTheory().term(SMTLIBConstants.NOT, pivot);
		for (final Term antLit : antecedentInfo.getLiterals()) {
			if (antLit != negPivot) {
				literals.add(antLit);
			}
		}
		mLiterals = literals.toArray(new Term[literals.size()]);
	}

	private static Term[] computeLiterals(final Object[] rawLits) {
		assert rawLits.length % 2 == 0;
		final Term[] literals = new Term[rawLits.length / 2];
		for (int i = 0; i < literals.length; i++) {
			final Term atom = (Term) rawLits[2 * i + 1];
			literals[i] = rawLits[2 * i] == "+" ? atom : atom.getTheory().term(SMTLIBConstants.NOT, atom);
		}
		return literals;
	}

	/**
	 * Checks if this proof clause is a resolution node.
	 *
	 * @return true if this is a resolution node.
	 */
	public boolean isResolution() {
		return mNodeKind == ClauseKind.RESOLUTION;
	}

	/**
	 * Checks if this proof clause is a leaf node, i.e., a lemma or a clause.
	 *
	 * @return true if this is a leaf node.
	 */
	public boolean isLeaf() {
		return mNodeKind != ClauseKind.RESOLUTION;
	}

	/**
	 * Gets the leaf kind, i.e., {@code @lemma} or {@code @clause}.
	 *
	 * @return the leaf kind.
	 */
	public ClauseKind getLeafKind() {
		return mNodeKind;
	}

	/**
	 * Gets the lemma type, i.e., the key of the lemma annotation. This should be
	 * one of :EQ, :cong, :trans, :LA or :trichotomy.
	 *
	 * @return the leaf kind.
	 */
	public String getLemmaType() {
		return mLemmaAnnotation.getKey();
	}

	/**
	 * Gets the lemma annotation, i.e., the value of the lemma annotation.
	 *
	 * @return the annotation object.
	 */
	public Object getLemmaAnnotation() {
		return mLemmaAnnotation.getValue();
	}

	/**
	 * Gets the literals. This may be null for resolution nodes, if the literals have not been computed.
	 *
	 * @return the literals.
	 */
	public Term[] getLiterals() {
		return mLiterals;
	}

	/**
	 * Gets the proof term for the primary clause. This is only valid for resolution nodes.
	 *
	 * @return the primary clause.
	 */
	public Term getPivotLiteral() {
		return mResolutionArgs[0];
	}

	/**
	 * Gets the proof terms for the antecedents. This is only valid for resolution nodes.
	 *
	 * @return the antecedents; each is annotated with the pivot literal.
	 */
	public Term[] getResolutionArgs() {
		return mResolutionArgs;
	}

	public String getSource() {
		assert mNodeKind == ClauseKind.INPUT;
		return (String) mLemmaAnnotation.getValue();
	}
}