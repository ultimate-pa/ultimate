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

import java.util.Arrays;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

/**
 * This class is used to gather the information from a proof term which is relevant for the interpolator.
 *
 * @author Tanja Schindler
 */
public class InterpolatorClauseTermInfo {

	/**
	 * The literals of this clause. This may be null for resolution clauses, if the literals haven't been computed yet.
	 * For leaf clauses this is always set correctly.
	 */
	private Term[] mLiterals;

	/**
	 * The type of this leaf term, i.e. lemma or clause
	 */
	private final String mNodeKind;

	/**
	 * The arguments of this resolution term
	 */
	private Term[] mResolutionArgs;

	/**
	 * The source partition of this input term or literal
	 */
	private String mSource;

	/**
	 * The lemma annotation, if this is a lemma leaf node.
	 */
	private Annotation mLemmaAnnotation;

	/**
	 * Create the information for a proof term representing a clause. This fills in all relevant fields for the given
	 * proof term.
	 */
	public InterpolatorClauseTermInfo(final Term term) {
		mNodeKind = ((ApplicationTerm) term).getFunction().getName();
		if (isResolution()) {
			mResolutionArgs = ((ApplicationTerm) term).getParameters();
		} else {
			computeLeafTermInfo(term);
		}
	}

	/**
	 * Fill in the field mLiterals for this resolution term only if needed (i.e. if deep check is switched on)
	 */
	public void computeResolutionLiterals(final Interpolator interpolator) {
		assert isResolution();
		final LinkedHashSet<Term> literals = new LinkedHashSet<>();
		final InterpolatorClauseTermInfo primInfo = interpolator.mClauseTermInfos.get(getPrimary());
		literals.addAll(Arrays.asList(primInfo.getLiterals()));
		for (final AnnotatedTerm antecedent : getAntecedents()) {
			final Term pivot = computePivot(antecedent);
			final InterpolatorClauseTermInfo antecedentInfo =
					interpolator.mClauseTermInfos.get(antecedent.getSubterm());
			literals.remove(interpolator.mTheory.not(pivot));
			for (final Term antLit : antecedentInfo.getLiterals()) {
				if (antLit != pivot) {
					literals.add(antLit);
				}
			}
		}
		mLiterals = literals.toArray(new Term[literals.size()]);
	}

	/**
	 * Collect the information needed to interpolate this leaf term.
	 */
	private void computeLeafTermInfo(final Term leafTerm) {
		Term clause;
		if (mNodeKind.equals(ProofConstants.FN_LEMMA)) {
			final AnnotatedTerm innerLemma = (AnnotatedTerm) ((ApplicationTerm) leafTerm).getParameters()[0];
			mLemmaAnnotation = innerLemma.getAnnotations()[0];
			clause = innerLemma.getSubterm();
			mLiterals = computeLiterals(clause);
		} else if (mNodeKind.equals(ProofConstants.FN_CLAUSE)) {
			final AnnotatedTerm subProof = (AnnotatedTerm) ((ApplicationTerm) leafTerm).getParameters()[0];
			assert subProof.getAnnotations()[0].getKey().equals(ProofConstants.ANNOTKEY_PROVES);
			assert subProof.getAnnotations()[1].getKey().equals(ProofConstants.ANNOTKEY_INPUT);
			mSource = (String) subProof.getAnnotations()[1].getValue();
			mLiterals = (Term[]) subProof.getAnnotations()[0].getValue();
		} else {
			throw new AssertionError("Unknown leaf type");
		}
	}

	/**
	 * Compute the literals of the given clause.
	 */
	private Term[] computeLiterals(final Term clause) {
		if (clause instanceof ApplicationTerm && ((ApplicationTerm) clause).getFunction().getName().equals("or")) {
			final ApplicationTerm appLit = (ApplicationTerm) clause;
			return appLit.getParameters();
		} else if (clause instanceof ApplicationTerm
				&& ((ApplicationTerm) clause).getFunction().getName().equals("false")) {
			// empty clause
			return new Term[0];
		} else {
			// singleton clause
			return new Term[] { clause };
		}
	}

	/**
	 * For an antecedent of a hyper-resolution step, get the pivot term.
	 */
	private Term computePivot(final AnnotatedTerm term) {
		return (Term) term.getAnnotations()[0].getValue();
	}

	/**
	 * Checks if this proof clause is a resolution node.
	 *
	 * @return true if this is a resolution node.
	 */
	public boolean isResolution() {
		return mNodeKind.equals(ProofConstants.FN_RES);
	}

	/**
	 * Checks if this proof clause is a leaf node, i.e., a lemma or a clause.
	 *
	 * @return true if this is a leaf node.
	 */
	public boolean isLeaf() {
		return !isResolution();
	}

	/**
	 * Gets the leaf kind, i.e., {@code @lemma} or {@code @clause}.
	 *
	 * @return the leaf kind.
	 */
	public String getLeafKind() {
		return mNodeKind;
	}

	/**
	 * Gets the lemma type, i.e., the key of the lemma annotation. This should be one of :EQ, :CC, :LA or :trichotomy.
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
	public Term getPrimary() {
		return mResolutionArgs[0];
	}

	/**
	 * Gets the proof terms for the antecedents. This is only valid for resolution nodes.
	 *
	 * @return the antecedents; each is annotated with the pivot literal.
	 */
	public AnnotatedTerm[] getAntecedents() {
		final AnnotatedTerm[] antecedents = new AnnotatedTerm[mResolutionArgs.length - 1];
		System.arraycopy(mResolutionArgs, 1, antecedents, 0, antecedents.length);
		return antecedents;
	}

	public String getSource() {
		return mSource;
	}
}