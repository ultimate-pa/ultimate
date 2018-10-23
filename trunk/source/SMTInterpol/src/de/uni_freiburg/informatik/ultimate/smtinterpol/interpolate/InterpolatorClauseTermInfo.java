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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * This class is used to gather the information from a proof term which is relevant for the interpolator.
 *
 * @author Tanja Schindler
 */
public class InterpolatorClauseTermInfo {

	/**
	 * All literals occurring in this term
	 */
	private final ArrayList<Term> mLiterals;

	/**
	 * The type of this leaf term, i.e. lemma or clause
	 */
	private String mNodeKind;

	/**
	 * The type of this lemma, i.e. EQ, CC, LA, weakeq-ext, read-over-weakeq
	 */
	private String mLemmaType;

	/**
	 * The primary of this resolution term
	 */
	private Term mPrimary;

	/**
	 * The antecedents of this resolution term
	 */
	private AnnotatedTerm[] mAntecedents;

	/**
	 * The source partition of this input term or literal
	 */
	private String mSource;

	/**
	 * The disequality literal in this CC lemma
	 */
	private Term mDiseq;

	/**
	 * The paths in CC and array lemmata
	 */
	private ProofPath[] mPaths;
	/**
	 * The CC equality in this EQ lemma
	 */
	private Term mCCEq;

	/**
	 * The LA equality in this EQ lemma
	 */
	private Term mLAEq;

	/**
	 * The factor in this EQ lemma
	 */
	private Rational mLAFactor;

	/**
	 * The Literals of this LA lemma and their corresponding Farkas coefficients
	 */
	private HashMap<Term, Rational> mFarkasCoeffs;

	/**
	 * This class is used to store subpaths and weakpaths of CC and array lemmas in a way convenient for the
	 * interpolation procedure. It stores the path index for weakpaths (null for subpaths) and the path as an array of
	 * terms. This is the equivalent of ArrayAnnotation.IndexedPath with Terms instead of CCTerms.
	 */
	class ProofPath {
		private final Term mPathIndex;
		private final Term[] mPath;

		private ProofPath(final String type, final Object path) {
			if (type.equals(":subpath")) {
				assert (path instanceof Term[]);
				mPathIndex = null;
				mPath = (Term[]) path;
			} else {
				assert (path instanceof Object[]);
				assert (((Object[]) path)[0] instanceof Term && ((Object[]) path)[1] instanceof Term[]);
				mPathIndex = (Term) ((Object[]) path)[0];
				mPath = (Term[]) ((Object[]) path)[1];
			}
		}

		public Term getIndex() {
			return mPathIndex;
		}

		public Term[] getPath() {
			return mPath;
		}
	}

	public InterpolatorClauseTermInfo() {
		mNodeKind = null;
		mLemmaType = null;
		mLiterals = new ArrayList<Term>();
		mPrimary = null;
		mAntecedents = null;

		mSource = null;

		mDiseq = null;
		mPaths = null;

		mCCEq = null;
		mLAEq = null;
		mLAFactor = null;
		mFarkasCoeffs = null;
	}

	/**
	 * Fill in all relevant fields for the given proof term.
	 */
	public void computeClauseTermInfo(final Term term) {
		mNodeKind = computeNodeKind(term);
		if (isResolution()) {
			computeResolutionTermInfo(term);
		} else {
			computeLeafTermInfo(term);
		}
	}

	/**
	 * Fill in the field mLiterals for this resolution term only if needed (i.e. if deep check is switched on)
	 */
	public void computeResolutionLiterals(final Interpolator interpolator) {
		assert isResolution();
		final LinkedHashSet<Term> literals = new LinkedHashSet<Term>();
		final InterpolatorClauseTermInfo primInfo = interpolator.mClauseTermInfos.get(mPrimary);
		literals.addAll(primInfo.getLiterals());
		for (final AnnotatedTerm antecedent : mAntecedents) {
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
		mLiterals.addAll(literals);
	}

	/**
	 * Collect the information needed to interpolate this resolution term.
	 */
	private void computeResolutionTermInfo(final Term term) {
		ApplicationTerm resTerm;
		if (term instanceof AnnotatedTerm) {
			resTerm = (ApplicationTerm) ((AnnotatedTerm) term).getSubterm();
		} else {
			resTerm = (ApplicationTerm) term;
		}
		final Term[] params = resTerm.getParameters();
		final AnnotatedTerm[] antes = new AnnotatedTerm[params.length - 1];
		for (int i = 0; i < params.length - 1; i++) {
			antes[i] = (AnnotatedTerm) params[i + 1];
		}
		mPrimary = params[0];
		mAntecedents = antes;
	}

	/**
	 * Collect the information needed to interpolate this leaf term.
	 */
	private void computeLeafTermInfo(final Term leafTerm) {
		mLiterals.addAll(computeLiterals(leafTerm));
		if (mNodeKind.equals("@lemma")) {
			final String lemmaType = computeLemmaType(leafTerm);
			if (lemmaType.equals(":EQ")) {
				computeEQLemmaInfo(leafTerm);
			} else if (lemmaType.equals(":CC") || lemmaType.equals(":weakeq-ext")
					|| lemmaType.equals(":read-over-weakeq") || lemmaType.equals(":const-weakeq")
					|| lemmaType.equals(":read-const-weakeq")) {
				computeCCLemmaInfo(leafTerm); // TODO This recomputes the lemma type.
			} else if (lemmaType.equals(":LA") || lemmaType.equals(":trichotomy")) {
				computeLALemmaInfo(leafTerm); // TODO This recomputes the lemma type.
			} else {
				throw new IllegalArgumentException("Unknown lemma type!");
			}
		} else if (mNodeKind.equals("@clause")) {
			AnnotatedTerm inputTerm = (AnnotatedTerm) ((ApplicationTerm) leafTerm).getParameters()[1];
			assert inputTerm.getAnnotations()[0].getKey().equals(":input");
			mSource = (String) inputTerm.getAnnotations()[0].getValue();
		} else {
			throw new AssertionError("Unknown leaf type");
		}
	}

	/**
	 * Collect the information needed to interpolate this EQ lemma
	 */
	private void computeEQLemmaInfo(final Term term) {
		mLemmaType = ":EQ";
		final Object[] eqParams = computeLiterals(term).toArray();
		Term term1 = (Term) eqParams[0];
		Term term2 = (Term) eqParams[1];
		assert ((isNegated(term1) && !isNegated(term2)) || (!isNegated(term1) && isNegated(term2)));
		if (isLAEquality(computeAtom(term1))) {
			term1 = (Term) eqParams[1];
			term2 = (Term) eqParams[0];
		}
		mCCEq = term1;
		mLAEq = term2;
		mLAFactor = computeLAFactor(computeAtom(term1), computeAtom(term2));
	}

	/**
	 * Collect the information needed to interpolate this CC lemma
	 */
	private void computeCCLemmaInfo(final Term term) {
		mLemmaType = computeLemmaType(term);
		mDiseq = computeDiseq(term);
		mPaths = computePaths(term);
	}

	/**
	 * Collect the information needed to interpolate this LA lemma
	 */
	private void computeLALemmaInfo(final Term term) {
		mLemmaType = computeLemmaType(term);
		final AnnotatedTerm inner = (AnnotatedTerm) ((ApplicationTerm) term).getParameters()[0];
		mFarkasCoeffs = computeCoefficients(inner);
	}

	/**
	 * Compute the kind of a leaf proof term
	 */
	private String computeNodeKind(final Term term) {
		return ((ApplicationTerm) term).getFunction().getName();
	}

	/**
	 * Compute the literals of this leaf term
	 */
	private LinkedHashSet<Term> computeLiterals(final Term term) {
		final LinkedHashSet<Term> literals = new LinkedHashSet<Term>();
		final String leafKind = computeNodeKind(term);
		Term clause;
		if (leafKind.equals("@lemma")) {
			final AnnotatedTerm innerLemma = (AnnotatedTerm) ((ApplicationTerm) term).getParameters()[0];
			clause = innerLemma.getSubterm();
		} else if (leafKind.equals("@clause")) {
			final AnnotatedTerm annotLit = (AnnotatedTerm) ((ApplicationTerm) term).getParameters()[1];
			clause = annotLit.getSubterm();
		} else {
			throw new AssertionError("There is another leafkind which has not yet been implemented.");
		}
		if (clause instanceof ApplicationTerm && ((ApplicationTerm) clause).getFunction().getName().equals("or")) {
			final ApplicationTerm appLit = (ApplicationTerm) clause;
			for (final Term arg : appLit.getParameters()) {
				literals.add(arg);
			}
		} else if (clause instanceof ApplicationTerm
				&& ((ApplicationTerm) clause).getFunction().getName().equals("false")) {
			// empty clause
		} else {
			literals.add(clause);
		}
		return literals;

	}

	/**
	 * For an antecedent of a hyper-resolution step, get the pivot term.
	 */
	private Term computePivot(final AnnotatedTerm term) {
		return (Term) term.getAnnotations()[0].getValue();
	}

	/**
	 * For a lemma term, get the theory which created the lemma
	 */
	private String computeLemmaType(final Term term) {
		final AnnotatedTerm innerLemma = (AnnotatedTerm) ((ApplicationTerm) term).getParameters()[0];
		return innerLemma.getAnnotations()[0].getKey();
	}

	/**
	 * Compute the LA factor for this EQ lemma. This is the factor f, such that
	 * <code>f * (ccEq.getLhs() - ccEq.getRhs()) == laEq.getLhs())</code>
	 */
	private Rational computeLAFactor(final Term ccEq, final Term laEq) {
		final InterpolatorAffineTerm ccLeft = Interpolator.termToAffine(((ApplicationTerm) ccEq).getParameters()[0]);
		final InterpolatorAffineTerm ccRight = Interpolator.termToAffine(((ApplicationTerm) ccEq).getParameters()[1]);
		final InterpolatorAffineTerm ccAffine = new InterpolatorAffineTerm(ccLeft);
		ccAffine.add(Rational.MONE, ccRight);
		final InterpolatorAffineTerm laAffine = Interpolator.termToAffine(((ApplicationTerm) laEq).getParameters()[0]);
		Rational factor = laAffine.getGCD().div(ccAffine.getGCD());
		final InterpolatorAffineTerm eqSum =
				new InterpolatorAffineTerm(ccAffine).mul(factor).add(Rational.MONE, laAffine);
		if (!eqSum.isConstant() || !eqSum.getConstant().equals(InfinitNumber.ZERO)) {
			factor = factor.negate();
			assert eqSum.add(Rational.TWO, laAffine).isConstant() && eqSum.getConstant().equals(InfinitNumber.ZERO);
		}
		return factor;
	}

	/**
	 * Compute the literals and corresponding Farkas coefficients for this LA lemma
	 */
	private HashMap<Term, Rational> computeCoefficients(final AnnotatedTerm annotTerm) {
		final Annotation annot = annotTerm.getAnnotations()[0];
		final HashMap<Term, Rational> coeffMap = new HashMap<Term, Rational>();
		Term term;
		Rational coeff;
		final Term[] subs = ((ApplicationTerm) annotTerm.getSubterm()).getParameters();
		final Object[] coeffs = (Object[]) annot.getValue();
		if (coeffs == null) { // trichotomy
			for (int i = 0; i < 3; i++) {
				term = subs[i];
				if (isLAEquality(computeAtom(term))) {
					coeffMap.put(term, Rational.ONE);
				} else {
					coeffMap.put(term, isNegated(term) ? Rational.ONE : Rational.MONE);
				}
			}
			return coeffMap;
		}
		for (int i = 0; i < coeffs.length; i++) {
			term = subs[i];
			coeff = SMTAffineTerm.convertConstant((ConstantTerm) coeffs[i]);
			coeffMap.put(term, coeff);
		}
		return coeffMap;
	}

	/**
	 * For a CC or array lemma, get the disequality explained by this lemma.
	 *
	 * @param lemma
	 * @return
	 */
	private Term computeDiseq(final Term lemma) {
		final AnnotatedTerm inner = (AnnotatedTerm) ((ApplicationTerm) lemma).getParameters()[0];
		final Annotation annotation = inner.getAnnotations()[0];
		final Object value = ((Object[]) annotation.getValue())[0];
		if (value instanceof Term) {
			return (Term) value;
		}
		return null;
	}

	/**
	 * For a CC or array lemma, get the sub- and weak paths.
	 *
	 * @return paths an array containing the proof paths
	 */
	private ProofPath[] computePaths(final Term lemma) {
		final AnnotatedTerm inner = (AnnotatedTerm) ((ApplicationTerm) lemma).getParameters()[0];
		final Annotation annotation = inner.getAnnotations()[0];
		assert annotation.getValue() instanceof Object[];
		final boolean hasDiseq = ((Object[]) annotation.getValue())[0] instanceof Term;
		final int length = (((Object[]) annotation.getValue()).length - (hasDiseq ? 1 : 0)) / 2;
		final ProofPath[] paths = new ProofPath[length];
		for (int i = 0; i < length; i++) {
			final int j = 2 * i + (hasDiseq ? 1 : 0);
			final String type = (String) ((Object[]) annotation.getValue())[j];
			final Object[] path = (Object[]) ((Object[]) annotation.getValue())[j + 1];
			paths[i] = new ProofPath(type, path);
		}
		return paths;
	}

	/**
	 * Compute the underlying atomic term for an annotated or negated term
	 */
	private Term computeAtom(final Term term) {
		Term inner = term;
		if (isNegated(inner)) {
			inner = ((ApplicationTerm) inner).getParameters()[0];
		}
		if (inner instanceof AnnotatedTerm) {
			inner = ((AnnotatedTerm) inner).getSubterm();
		}
		return inner;
	}

	/**
	 * Check if a term is negated
	 */
	private boolean isNegated(Term term) {
		if (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm) term).getSubterm();
		}
		if ((term instanceof ApplicationTerm)) {
			return ((ApplicationTerm) term).getFunction().getName().equals("not");
		} else {
			return false;
		}
	}

	/**
	 * Check if this atom is a LA equality. Note that some CC equalities look like LA equalities, but in those cases,
	 * they are treated the same way.
	 */
	private boolean isLAEquality(final Term atom) {
		if ((atom instanceof ApplicationTerm)) {
			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				final Term secondParam = ((ApplicationTerm) atom).getParameters()[1];
				if ((secondParam instanceof ConstantTerm)) {
					return SMTAffineTerm.convertConstant((ConstantTerm) secondParam).equals(Rational.ZERO);
				}
			}
		}
		return false;
	}

	public boolean isResolution() {
		return mNodeKind.equals("@res");
	}

	public boolean isLeaf() {
		return !isResolution();
	}

	public String getLeafKind() {
		return mNodeKind;
	}

	public String getLemmaType() {
		return mLemmaType;
	}

	public ArrayList<Term> getLiterals() {
		return mLiterals;
	}

	public Term getPrimary() {
		return mPrimary;
	}

	public AnnotatedTerm[] getAntecedents() {
		return mAntecedents;
	}

	public String getSource() {
		return mSource;
	}

	public Term getDiseq() {
		return mDiseq;
	}

	public ProofPath[] getPaths() {
		return mPaths;
	}

	public Term getCCEq() {
		return mCCEq;
	}

	public Term getLAEq() {
		return mLAEq;
	}

	public Rational getLAFactor() {
		return mLAFactor;
	}

	public HashMap<Term, Rational> getFarkasCoeffs() {
		return mFarkasCoeffs;
	}
}