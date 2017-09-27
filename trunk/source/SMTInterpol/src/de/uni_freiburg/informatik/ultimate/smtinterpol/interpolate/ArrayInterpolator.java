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

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseTermInfo.ProofPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the theory of arrays.
 *
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class ArrayInterpolator {

	/* General info to set up the ArrayInterpolator */
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	/**
	 * The conjuncts or disjuncts that build the interpolants.
	 */
	private Set<Term>[] mInterpolants;

	/* Information for array lemmas */
	/**
	 * Information about the lemma proof term.
	 */
	private InterpolatorClauseTermInfo mLemmaInfo;
	/**
	 * The main disequality of this lemma. It is of the form "a[i]!=b[j]" for read-over-weakeq lemmas, and of the form
	 * "a!=b" for weakeq-ext lemmas.
	 */
	private ApplicationTerm mDiseq;
	/**
	 * The LitInfo for the main disequality of this lemma.
	 */
	private LitInfo mDiseqInfo;
	/**
	 * The atoms of the equality literals in the lemma that is interpolated. Note that they appear negated in the lemma
	 * clause.
	 */
	private Map<SymmetricPair<Term>, ApplicationTerm> mEqualities;
	/**
	 * The atoms of the disequality literals in the lemma that is interpolated. Note that they appear positively in the
	 * lemma clause.
	 */
	private Map<SymmetricPair<Term>, ApplicationTerm> mDisequalities;
	/**
	 * The store path between the arrays of the main disequality for weak equivalence a weakeq-ext lemma, and for weak
	 * equivalence modulo i, where i is the path index, in a read-over-weakeq lemma.
	 */
	private ProofPath mStorePath;
	/**
	 * This determines in which way we build the interpolant in weakeq-ext, particularly for the mixed case. Note that
	 * the naming is a bit counterintuitive, as B-interpolated means we summarize A-paths. This results from the fact
	 * that we do this when the main disequality is in B.
	 */
	private boolean[] mIsBInterpolated;

	/* Specific information for read-over-weakeq-lemmas */
	/**
	 * The strong path between the select indices of the main disequality.
	 */
	private ApplicationTerm mIndexEquality;
	/**
	 * This contains the shared select index for all partitions where it exists.
	 */
	private Term[] mSharedIndex;

	// Specific information for weakeq-ext-lemmas
	/**
	 * This map contains the paths for weak congruence on index i.
	 */
	private Map<Term, ProofPath> mIndexPaths;
	/**
	 * The term on the side of the main path from which we recurse. Only needed for mixed weakeq-ext.
	 */
	private Term[] mRecursionSide;
	/**
	 * The auxiliary variable that is used to build the recursive interpolant in mixed weakeq-ext lemmas.
	 */
	private TermVariable mRecursionVar;

	@SuppressWarnings("unchecked")
	public ArrayInterpolator(final Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<Term>();
		}
	}

	/**
	 * Compute interpolants for array lemmas of type read-over-weakeq and weakeq-ext.
	 *
	 * @param proofTerm
	 *            The lemma that is interpolated
	 * @return An array containing interpolants for the different partitions
	 */
	public Term[] computeInterpolants(final Term proofTerm) {
		mLemmaInfo = mInterpolator.getClauseTermInfo(proofTerm);
		mDiseq = (ApplicationTerm) mLemmaInfo.getDiseq();
		mDiseqInfo = mInterpolator.getLiteralInfo(mDiseq);
		mEqualities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		mDisequalities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		mIsBInterpolated = new boolean[mNumInterpolants];
		for (final Term literal : mLemmaInfo.getLiterals()) {
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(literal);
			if (litTermInfo.isNegated()) {
				final ApplicationTerm eq = (ApplicationTerm) litTermInfo.getAtom();
				mEqualities.put(new SymmetricPair<Term>(eq.getParameters()[0], eq.getParameters()[1]), eq);
			} else {
				final ApplicationTerm diseq = (ApplicationTerm) litTermInfo.getAtom();
				mDisequalities.put(new SymmetricPair<Term>(diseq.getParameters()[0], diseq.getParameters()[1]), diseq);
			}
		}

		Term[] interpolants = new Term[mNumInterpolants];
		if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
			interpolants = computeReadOverWeakeqInterpolants(proofTerm);
		} else {
			assert mLemmaInfo.getLemmaType().equals(":weakeq-ext");
			interpolants = computeWeakeqExtInterpolants(proofTerm);
		}
		FormulaUnLet unletter = new FormulaUnLet();
		for (int i = 0; i < mNumInterpolants; i++) {
			interpolants[i] = unletter.unlet(interpolants[i]);
		}
		return interpolants;
	}

	/**
	 * Compute interpolants for a read-over-weakeq lemma. The lemma consists of a disequality of form "a[i] != b[j]", a
	 * (strong) path of length 2 for the index equality "i = j" unless the disequality is of form "a[i] != b[i]", and a
	 * weak path from array "a" to array "b" consisting of equality or store steps with store operations only at indices
	 * different from the weakpath index, which is one of the select indices. We distinguish four cases for
	 * interpolation: either (i) there is a shared index term and the main diseq is in B or mixed -> terms of the form
	 * "s1[x]=s2[x]" for A-paths; or (ii) there is a shared index term and the main diseq is A local -> terms of the
	 * form "s1[x]!=s2[x]" for B paths; or (iii) both i,j are B-local -> terms of the form "weq(s1,s2,k,F(·))" are built
	 * for A paths; or (iv) both i,j are A-local -> terms of the form "nweq(s1,s2,k,F(·))" are built for B paths.
	 *
	 * @param proofTerm
	 *            The lemma which interpolants are calculated for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeReadOverWeakeqInterpolants(final Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length <= 2;
		if (paths.length == 2) {
			final Term[] indexPath;
			if (paths[0].getIndex() == null) {
				indexPath = paths[0].getPath();
				mStorePath = paths[1];
			} else {
				indexPath = paths[1].getPath();
				mStorePath = paths[0];
			}
			assert indexPath.length == 2;
			mIndexEquality = mEqualities.get(new SymmetricPair<Term>(indexPath[0], indexPath[1]));
		} else { // In this case, the main disequality is of form "a[i] != b[i]"
			assert paths.length == 1;
			mStorePath = paths[0];
		}

		final WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);

		determineInterpolationColor();

		// Determine the shared select index for all partitions where it exists
		computeSharedSelectIndices();
		// Calculate the interpolant terms from the store path
		mInterpolants = arrayPath.interpolateWeakPathInfo();
		// In some cases, the index equality has to be added
		if (mIndexEquality != null) {
			addIndexEqualityReadOverWeakeq();
		}
		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mDiseqInfo.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
				interpolants[color] = mTheory.or(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			} else { // the interpolant is the conjunction of all path interpolants
				interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			}
		}
		return interpolants;
	}

	/**
	 * Compute interpolants for a weakeq-ext lemma. The lemma consists of a disequality of form "a != b", a weak path
	 * from array "a" to array "b" consisting of equality and store steps, and for each index "i" on this path a weak
	 * path indexed with "i" that ensures that "a" and "b" are weakly congruent on "i". There are three base cases for
	 * interpolation: "a != b" is (i) B-local (ii) A-local (iii) mixed.
	 *
	 * @param proofTerm
	 *            The lemma which interpolants are calculated for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeWeakeqExtInterpolants(final Term proofTerm) {
		// TODO In the mixed case, it makes sense to choose the interpolation color depending on the number of stores on
		// the outer A and B paths on the main path.
		// TODO Index paths that are used several times should not be interpolated again (do not use "new WeakPath" if
		// not necessary)
		final ProofPath[] paths = mLemmaInfo.getPaths();
		mStorePath = paths[0];
		mIndexPaths = new HashMap<Term, ProofPath>();
		for (int i = 1; i < paths.length; i++) {
			mIndexPaths.put(paths[i].getIndex(), paths[i]);
		}

		final WeakPathInfo mainPath = new WeakPathInfo(mStorePath);

		// Calculate the interpolant terms starting on the store path.
		mInterpolants = mainPath.interpolateStorePathInfoExt();
		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (!mDiseqInfo.isMixed(color)) {
				if (mDiseqInfo.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
					interpolants[color] =
							mTheory.or(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				} else { // the interpolant is the conjunction of all path interpolants
					interpolants[color] =
							mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				}
			} else {
				interpolants[color] = mInterpolants[color].iterator().next(); // There should be only one term
			}
		}
		return interpolants;
	}

	/**
	 * Determine for all partitions whether there exists a shared select index. This can be the weakpathindex, if no
	 * index equality exists; the mixed variable if the index equality is mixed; the weakpathindex if the index equality
	 * is local or shared; the other select index if the index equality is A- or B-local and weakpathindex is not
	 * shared. Note: if both select indices are shared, take weakpathindex. This information is used during
	 * interpolation to determine the partitions where a simple interpolant can be built.
	 */
	private void computeSharedSelectIndices() {
		mSharedIndex = new Term[mNumInterpolants];
		// If the main disequality is of form "a[i] != b[i]", there is no path for the index equality
		if (mIndexEquality == null) {
			// Check if the weakpath index is shared
			final Term index = mStorePath.getIndex();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mInterpolator.getOccurrence(index, null).isAB(color)) {
					mSharedIndex[color] = index;
				}
			}
		} else {
			for (int color = 0; color < mNumInterpolants; color++) {
				// Check if the weakpath index is shared
				if (mInterpolator.getOccurrence(mStorePath.getIndex(), null).isAB(color)) {
					mSharedIndex[color] = mStorePath.getIndex();
				} else {
					final LitInfo info = mInterpolator.getLiteralInfo(mIndexEquality);
					// Check if there is a mixed variable
					if (info.isMixed(color)) {
						mSharedIndex[color] = info.getMixedVar();
					} else { // Check the other select index
						assert info.isALocal(color) || info.isBLocal(color);
						Term otherIndex = mIndexEquality.getParameters()[0];
						otherIndex =
								otherIndex == mStorePath.getIndex() ? mIndexEquality.getParameters()[1] : otherIndex;
						if (mInterpolator.getOccurrence(otherIndex, null).isAB(color)) {
							mSharedIndex[color] = otherIndex;
						}
					}
				}
			}
		}
	}

	/**
	 * For a given term, if the term itself is not shared, find an equality literal containing this term and a shared
	 * term on the other side, or a mixed equality.
	 *
	 * @param term
	 *            the term for which we want to find shared terms for all partitions (it can be shared itself)
	 * @param color
	 *            the current partition
	 * @return some shared term which equals the given term, or null if there is none
	 */
	private Term findSharedTerm(final Term term, final int color) {
		Term sharedTerm = null;
		final Occurrence termOccur = mInterpolator.getOccurrence(term, null);
		if (termOccur.isAB(color)) {
			sharedTerm = term;
		} else { // go through the equalities
			for (final SymmetricPair<Term> eq : mEqualities.keySet()) {
				if (eq.getFirst().equals(term) || eq.getSecond().equals(term)) {
					final LitInfo eqInfo = mInterpolator.getLiteralInfo(mEqualities.get(eq));
					if (eqInfo.isMixed(color)) {
						sharedTerm = eqInfo.getMixedVar();
						break;
					} else {
						final Term otherTerm = eq.getFirst().equals(term) ? eq.getSecond() : eq.getFirst();
						final Occurrence otherOccur = mInterpolator.getOccurrence(otherTerm, null);
						if (otherOccur.isAB(color)) {
							sharedTerm = otherTerm;
							break;
						}
					}
				}
			}
		}
		return sharedTerm;
	}

	/**
	 * Determine how the lemma is interpolated. We say that it is 'B-interpolated' if we summarize A-paths. This
	 * counterintuitive notation results from the fact that we do this when mDiseq is in B. For weakeq-ext, this should
	 * be called after setting mRecursionSide.
	 */
	private void determineInterpolationColor() {
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mDiseqInfo.isALocal(color)) {
				mIsBInterpolated[color] = false;
			} else if (mDiseqInfo.isBorShared(color) || mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
				mIsBInterpolated[color] = true;
			} else { // Mixed diseq in weakeq-ext
				final Occurrence recursionInfo = mInterpolator.getOccurrence(mRecursionSide[color], null);
				mIsBInterpolated[color] = recursionInfo.isALocal(color);
			}
		}
	}

	/**
	 * For read-over-weakeq, the index equality has to be included in the interpolant if both indices are shared and
	 * either a) it is A-local and the main diseq is mixed or B -> it is added as conjunct to the interpolant, or b) it
	 * is B-local and the main diseq is A -> it is a premise for the path summaries
	 */
	private void addIndexEqualityReadOverWeakeq() {
		final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
		final Term otherSelect = // not the select with the store path index
				getIndexFromSelect(mDiseq.getParameters()[0]).equals(mStorePath.getIndex()) ? mDiseq.getParameters()[1]
						: mDiseq.getParameters()[0];
		final Occurrence otherSelectOccur = mInterpolator.getOccurrence(otherSelect, null);
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mSharedIndex[color] != null && mSharedIndex[color] == mStorePath.getIndex()) {
				if (mDiseqInfo.isALocal(color) && indexEqInfo.isBLocal(color)) {
					mInterpolants[color].add(mTheory.not(mIndexEquality));
				} else if (indexEqInfo.isALocal(color) && otherSelectOccur.isBorShared(color)) {
					mInterpolants[color].add(mIndexEquality);
				}
			}
		}
	}

	/* Methods for tree interpolation */

	/**
	 * Compute the parent partition. This is the next partition whose subtree includes color.
	 */
	private int getParent(final int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child that is A-local to the occurrence. This function returns
	 * -1 if all children are in B.
	 */
	private int getChild(final int color, final Occurrence occur) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	/* Methods to deal with array terms */

	private static boolean isSelectTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("select");
		}
		return false;
	}

	private static boolean isStoreTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("store");
		}
		return false;
	}

	private static Term getArrayFromSelect(final Term select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[0];
	}

	private static Term getIndexFromSelect(final Term select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[1];
	}

	private static Term getArrayFromStore(final Term store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[0];
	}

	private static Term getIndexFromStore(final Term store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[1];
	}

	/**
	 * Build a select equality for given array terms and index. If the path ended with a mixed select equality (in
	 * weakeq-ext), the select term at this end is the mixedVar.
	 *
	 * @param left
	 *            the shared array at the left path end, or a mixed select eq.
	 * @param right
	 *            the shared array at the right path end, or a mixed select eq.
	 * @param index
	 *            the shared index for which the arrays match, i.e. the shared term for the weakpath index.
	 * @return a term of the form "left[index]=right[index]"
	 */
	private Term buildSelectEq(final Term left, final Term right, final Term index) {
		final Term leftSelect;
		if (left instanceof ApplicationTerm && mEqualities.containsValue(left)) {
			final LitInfo selectEq = mInterpolator.getLiteralInfo(left);
			leftSelect = selectEq.getMixedVar();
		} else {
			leftSelect = mTheory.term("select", left, index);
		}
		final Term rightSelect;
		if (right instanceof ApplicationTerm && mEqualities.containsValue(right)) {
			final LitInfo selectEq = mInterpolator.getLiteralInfo(right);
			rightSelect = selectEq.getMixedVar();
		} else {
			rightSelect = mTheory.term("select", right, index);
		}
		return mTheory.equals(leftSelect, rightSelect);
	}

	/**
	 * Build a weq term for two arrays and a given formula F. It states that two arrays differ at most at #stores
	 * positions, and each difference satisfies F.
	 *
	 * @param left
	 *            the shared array at the left path end
	 * @param right
	 *            the shared array at the right path end
	 * @param order
	 *            the order (= #stores) of the weq term
	 * @param formula
	 *            the formula satisfied by the diff terms, with an auxiliary variable
	 * @param auxVar
	 *            the auxiliary variable in the formula
	 * @return
	 */
	private Term buildWeqTerm(final Term left, final Term right, final int order, final Term formula,
			final TermVariable auxVar) {
		Term rewrite = left;
		Term weqTerm = mTheory.mTrue;

		for (int m = 0; m < order; m++) {
			final Term arrayEquality = mTheory.equals(rewrite, right);
			final Term diffTerm = mTheory.term("@diff", rewrite, right);
			final Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			weqTerm = mTheory.and(weqTerm, mTheory.or(arrayEquality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		weqTerm = mTheory.and(weqTerm, mTheory.equals(rewrite, right));

		return weqTerm;
	}

	/**
	 * Build an nweq term for two arrays and a given formula F. It states that two arrays differ at some index that
	 * satisfies F or on more than #stores indices.
	 *
	 * @param left
	 *            the shared array at the left path end
	 * @param right
	 *            the shared array at the right path end
	 * @param order
	 *            the order (= #stores) of the nweq term
	 * @param formula
	 *            the formula satisfied by the diff terms, with an auxiliary variable
	 * @param auxVar
	 *            the auxiliary variable in the formula
	 * @return
	 */
	private Term buildNweqTerm(final Term left, final Term right, final int order, final Term formula,
			final TermVariable auxVar) {
		Term rewrite = left;
		Term nweqTerm = mTheory.mFalse;

		for (int m = 0; m < order; m++) {
			final Term arrayDisequality = mTheory.not(mTheory.equals(rewrite, right));
			final Term diffTerm = mTheory.term("@diff", rewrite, right);
			final Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			nweqTerm = mTheory.or(nweqTerm, mTheory.and(arrayDisequality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		nweqTerm = mTheory.or(nweqTerm, mTheory.not(mTheory.equals(rewrite, right)));

		return nweqTerm;
	}

	/**
	 * This class interpolates a single weak path.
	 */
	class WeakPathInfo {
		/**
		 * The index determines at which position the arrays on this path are guaranteed to coincide. On the main path
		 * of a weakeq-ext lemma it is null.
		 */
		Term mPathIndex;
		/**
		 * The array containing the array terms on this path.
		 */
		Term[] mPath;
		/**
		 * The set of partitions for which there is an AB-shared path from start to end.
		 */
		BitSet mHasABPath;
		/**
		 * The first partition for which the path from start to end is A-local. This is mNumInterpolants, if there is no
		 * such partition. If mHasABPath is not empty, this value is undefined; we set it to the root of the mHasABPath
		 * tree, which equals the two mColor of the head and tail node.
		 */
		int mMaxColor;
		/**
		 * When interpolating mPath, this stores the information for a path which is not yet closed at the left side.
		 */
		WeakPathEnd mHead;
		/**
		 * When interpolating mPath, this stores the information for a path which is closed at the left side but still
		 * open on the right side.
		 */
		WeakPathEnd mTail;
		/**
		 * The conjuncts or disjuncts that build the path interpolants.
		 */
		private final Set<Term>[] mPathInterpolants;

		/* For index paths in weakeq-ext only */
		/**
		 * The conjuncts or disjuncts that build the path interpolants for the recursion in mixed weakeq-ext.
		 */
		private Set<Term>[] mRecursionInterpolants;

		/* For the store path in weakeq-ext only */
		/**
		 * This map stores for the inner A and B paths on the main path (for mixed weakeq-ext lemmas only) the number of
		 * store steps. This is used to build the nweq terms that find the index for recursion.
		 */
		private Map<SymmetricPair<Term>, Integer>[] mInnerPaths;

		boolean mComputed;

		@SuppressWarnings("unchecked")
		public WeakPathInfo(final ProofPath path) {
			mPathIndex = path.getIndex();
			mPath = path.getPath();
			mHasABPath = new BitSet(mNumInterpolants);
			mHasABPath.set(0, mNumInterpolants);
			mMaxColor = mNumInterpolants;
			mPathInterpolants = new Set[mNumInterpolants];
			for (int i = 0; i < mNumInterpolants; i++) {
				mPathInterpolants[i] = new HashSet<Term>();
			}
			if (mPathIndex == null) { // For weakeq-ext main path only
				mInnerPaths = new Map[mNumInterpolants];
				for (int i = 0; i < mNumInterpolants; i++) {
					mInnerPaths[i] = new HashMap<SymmetricPair<Term>, Integer>();
				}
			}
			if (mLemmaInfo.getLemmaType().equals(":weakeq-ext") && mPathIndex != null) {
				mRecursionInterpolants = new Set[mNumInterpolants];
			}
		}

		/**
		 * Compute the interpolants for the complete weakpath and all partitions for read-over-weakeq and the index
		 * paths of weakeq-ext.
		 */
		public Set<Term>[] interpolateWeakPathInfo() {
			if (mComputed) {
				return mPathInterpolants;
			}

			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			final Term[] diseqTerms = mDiseq.getParameters();

			// Depending on mDiseq, determine whether to start and end with A or B or AB.
			final Term headTerm, tailTerm;
			if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
				if (getArrayFromSelect(diseqTerms[0]).equals(mPath[0])) {
					headTerm = diseqTerms[0];
					tailTerm = diseqTerms[1];
				} else {
					headTerm = diseqTerms[1];
					tailTerm = diseqTerms[0];
				}
			} else { // TODO Do we have to do this for each index path for weakeq-ext?
				headTerm = mPath[0];
				tailTerm = mPath[mPath.length - 1];
			}
			final Occurrence headOccur = mInterpolator.getOccurrence(headTerm, null);
			final Occurrence tailOccur = mInterpolator.getOccurrence(tailTerm, null);

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm = left;

				// Each step in a weak path can be either an equality literal or a store step of form "a (store a k v)",
				// or, in weakeq-ext lemmas only, a select equality.
				// In the second and third case, there is no equality literal for the arrays in the lemma.
				if (lit == null) {
					if (mLemmaInfo.getLemmaType().equals(":weakeq-ext")) {
						// check if the step is a select equality
						final ApplicationTerm selectEq = findSelectEquality(left, right);
						if (selectEq != null) {
							final LitInfo stepInfo = mInterpolator.getLiteralInfo(selectEq);
							Term leftSelect, rightSelect;
							if (getArrayFromSelect(selectEq.getParameters()[0]) == left) {
								leftSelect = selectEq.getParameters()[0];
								rightSelect = selectEq.getParameters()[1];
							} else {
								leftSelect = selectEq.getParameters()[1];
								rightSelect = selectEq.getParameters()[0];
							}
							// Add the index equality for the first select term
							mTail.addSelectIndexEquality(mHead, leftSelect);
							mTail.closeAPath(mHead, boundaryTerm, stepInfo);
							mTail.openAPath(mHead, boundaryTerm, stepInfo);
							// If the equality is mixed in some partition, we open or close the path at the mixed
							// variable, storing the mixed equality as boundary term.
							if (stepInfo.getMixedVar() != null) {
								final Occurrence occ = mInterpolator.getOccurrence(rightSelect, null);
								boundaryTerm = selectEq;
								mTail.closeAPath(mHead, boundaryTerm, occ);
								mTail.openAPath(mHead, boundaryTerm, occ);
							}
							// The other index equality is added after opening/closing
							mTail.addSelectIndexEquality(mHead, rightSelect);
							continue;
						}
					}

					// Else, it is a store step. We store the index disequality "storeindex != weakpathindex" for the
					// interpolant if it is mixed, or if it is A-local on a B-path or vice versa.
					final Term storeTerm, arrayTerm;
					if (isStoreTerm(left) && getArrayFromStore(left).equals(right)) {
						storeTerm = left;
						arrayTerm = right;
					} else {
						storeTerm = right;
						arrayTerm = left;
					}
					assert getArrayFromStore(storeTerm).equals(arrayTerm);
					final Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm, null);
					final Term storeIndex = getIndexFromStore(storeTerm);
					final ApplicationTerm indexDiseq =
							mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
					final Occurrence indexDiseqOcc = mInterpolator.getLiteralInfo(indexDiseq);
					final Occurrence intersectOcc = stepOcc.intersect(indexDiseqOcc);

					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.closeAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addIndexDisequality(mHead, storeTerm);
				} else { // In equality steps, we just close or open A paths.
					final LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (stepInfo.getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right, null);
						boundaryTerm = stepInfo.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}

			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			// Paths which are still open at mPath[0] or mPath[mPath.length - 1] have to be closed.
			closeWeakPath();

			mComputed = true;
			return mPathInterpolants;
		}

		/**
		 * Interpolate the main path of weakeq-ext for all partitions. This also computes the interpolant terms for the
		 * index paths.
		 */
		public Set<Term>[] interpolateStorePathInfoExt() {
			if (mComputed) {
				return mPathInterpolants;
			}

			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			// Determine whether to start (and end) with A or B or AB and open A paths accordingly.
			final Term headArray = mPath[0];
			final Term tailArray = mPath[mPath.length - 1];
			final Occurrence headOccur = mInterpolator.getOccurrence(headArray, null);
			final Occurrence tailOccur = mInterpolator.getOccurrence(tailArray, null);

			if (mDiseqInfo.getMixedVar() != null) {
				// TODO Find shared arrays and determine recursion side:
				// For the mixed case, check if there is a shared array for mDiseq. In this case, we don't need to build
				// the recursive interpolant but interpolate in such way that all paths in either A or B are closed by
				// shared terms.
				// findSharedTerm(...);
				// If there is no shared array for mDiseq, count the number of stores on the outer paths on the main
				// path to determine which side needs less recursion steps.
				// determineRecursionSide();
				mRecursionSide = new Term[mNumInterpolants];
				// For now, we do the recursion on the left side
				for (int color = 0; color < mNumInterpolants; color++) {
					mRecursionSide[color] = mPath[0];
				}

				mRecursionVar = mTheory.createFreshTermVariable("recursive", mPath[0].getSort());
			}

			determineInterpolationColor();

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);
			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm;
				boundaryTerm = left;

				// Each step in the main path is either an equality literal or a store step of form "a (store a i v)".
				// In the second case, there is no literal in the lemma.
				if (lit == null) {
					// A store step can only open or close a path at term "a" if "a" is the left term;
					// we also open (resp. close) at shared stores if the index diseq "storeindex != weakpathindex" is
					// A-local (resp. B-local) to avoid collecting the diseq.
					// after this, we store the index disequality "storeindex != weakpathindex" for the interpolant if
					// it is mixed, or if it is A-local on a B-local path or vice versa.
					final Term storeTerm, arrayTerm;
					if (isStoreTerm(left) && getArrayFromStore(left).equals(right)) {
						storeTerm = left;
						arrayTerm = right;
					} else {
						storeTerm = right;
						arrayTerm = left;
					}
					assert getArrayFromStore(storeTerm).equals(arrayTerm);
					final Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm, null);
					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addStoreIndex(mHead, storeTerm);
				} else { // In equality steps, we just close or open A paths.
					final LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (stepInfo.getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right, null);
						boundaryTerm = stepInfo.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}
			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			// Paths which are still open at mPath[0] or mPath[mPath.length - 1] have to be closed.
			closeWeakeqExt(headOccur, tailOccur);

			mComputed = true;
			return mPathInterpolants;
		}

		/**
		 * This method computes the index path interpolant needed for the recursive interpolant in mixed weakeq-ext. It
		 * summarizes the inner index paths and is interpolated in the opposite way, i.e. by !mIsBInterpolated[color].
		 * This is only used in index paths of weakeq-ext.
		 *
		 * @param recursionTerm
		 *            The term to which we rewrite in the recursive interpolant.
		 * @param sharedIndex
		 *            The shared index used for this interpolation in this partition.
		 * @param color
		 *            This partition
		 * @return The index path interpolant for the recursive interpolant.
		 */
		public Set<Term> interpolateIndexPathForRecursion(final Term sharedIndex, final int color) {
			assert mComputed == false;
			if (mRecursionInterpolants[color] != null) { // has been interpolated for recursion before
				return mRecursionInterpolants[color];
			}

			// For this path and color, inverse mIsBInterpolated.
			mIsBInterpolated[color] = !mIsBInterpolated[color];
			// Set the shared index for this path and color
			if (mSharedIndex == null) {
				mSharedIndex = new Term[mNumInterpolants];
			}
			mSharedIndex[color] = sharedIndex;

			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			// Determine whether to start (and end) with A or B or AB and open A paths accordingly.
			final Occurrence headOccur = mInterpolator.getOccurrence(mPath[0], null);
			final Occurrence tailOccur = mInterpolator.getOccurrence(mPath[mPath.length - 1], null);

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm = left;

				// Each step in a weak path can be either an equality literal or a store step of form "a (store a k v)",
				// or, in weakeq-ext lemmas only, a select equality.
				// In the second and third case, there is no equality literal for the arrays in the lemma.
				if (lit == null) {
					// check if the step is a select equality
					final ApplicationTerm selectEq = findSelectEquality(left, right);
					if (selectEq != null) {
						final LitInfo stepInfo = mInterpolator.getLiteralInfo(selectEq);
						Term leftSelect, rightSelect;
						if (getArrayFromSelect(selectEq.getParameters()[0]) == left) {
							leftSelect = selectEq.getParameters()[0];
							rightSelect = selectEq.getParameters()[1];
						} else {
							leftSelect = selectEq.getParameters()[1];
							rightSelect = selectEq.getParameters()[0];
						}
						/*
						 * In partitions where selectEq was local, we have to add the index eqs to ... ... tail if we
						 * didn't open/close anything ... head if we did, in case the eq is mixed, or B-local on an
						 * A-path or vice versa.
						 */
						mTail.addSelectIndexEquality(mHead, leftSelect);
						mTail.closeAPath(mHead, boundaryTerm, stepInfo);
						mTail.openAPath(mHead, boundaryTerm, stepInfo);
						// If the equality is mixed in some partition, we open or close the path at the mixed
						// variable.
						if (stepInfo.getMixedVar() != null) {
							final Occurrence occ = mInterpolator.getOccurrence(rightSelect, null);
							boundaryTerm = selectEq;
							mTail.closeAPath(mHead, boundaryTerm, occ);
							mTail.openAPath(mHead, boundaryTerm, occ);
						}
						// the other index equality is added after opening/closing
						mTail.addSelectIndexEquality(mHead, rightSelect);
						continue;
					}

					/*
					 * Else, it is a store step. We store the index disequality "storeindex != weakpathindex" for the
					 * interpolant if it is mixed, or if it is A-local on a B-local path or vice versa.
					 */
					final Term storeTerm, arrayTerm;
					if (isStoreTerm(left) && getArrayFromStore(left).equals(right)) {
						storeTerm = left;
						arrayTerm = right;
					} else {
						storeTerm = right;
						arrayTerm = left;
					}
					assert getArrayFromStore(storeTerm).equals(arrayTerm);
					final Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm, null);
					final Term storeIndex = getIndexFromStore(storeTerm);
					final ApplicationTerm indexDiseq =
							mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
					final Occurrence indexDiseqOcc = mInterpolator.getLiteralInfo(indexDiseq);
					final Occurrence intersectOcc = stepOcc.intersect(indexDiseqOcc);

					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.closeAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addIndexDisequality(mHead, storeTerm);
				} else { // In equality steps, we just close or open A paths.
					final LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (stepInfo.getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right, null);
						boundaryTerm = stepInfo.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}

			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			// Restore the old mIsBInterpolated
			mIsBInterpolated[color] = !mIsBInterpolated[color];
			mRecursionInterpolants[color] = mPathInterpolants[color];
			return mRecursionInterpolants[color];
		}

		/**
		 * For a step in an index path of an extensionality lemma that is not an array equality, check if we can find a
		 * select equality between the arrays and corresponding index equalities.
		 *
		 * @return the select equality if it exists, else null.
		 */
		private ApplicationTerm findSelectEquality(final Term leftArray, final Term rightArray) {
			final SymmetricPair<Term> arrayPair = new SymmetricPair<Term>(leftArray, rightArray);
			for (final SymmetricPair<Term> testEq : mEqualities.keySet()) {
				// Find some select equality.
				final Term testLeft = testEq.getFirst();
				final Term testRight = testEq.getSecond();
				if (!(isSelectTerm(testLeft) && isSelectTerm(testRight))) {
					continue;
				}
				// Check if the arrays of the select terms match the term pair.
				final Term testLeftArray = getArrayFromSelect(testLeft);
				final Term testRightArray = getArrayFromSelect(testRight);
				final SymmetricPair<Term> testArrayPair = new SymmetricPair<Term>(testLeftArray, testRightArray);
				if (!arrayPair.equals(testArrayPair)) {
					continue;
				}
				// Check if the select indices equal the weakpath index (trivially or by an equality literal).
				final Term testLeftIndex = getIndexFromSelect(testLeft);
				final Term testRightIndex = getIndexFromSelect(testRight);
				if (testLeftIndex == mPathIndex
						|| mEqualities.containsKey(new SymmetricPair<Term>(testLeftIndex, mPathIndex))) {
					if (testRightIndex == mPathIndex
							|| mEqualities.containsKey(new SymmetricPair<Term>(testRightIndex, mPathIndex))) {
						return mEqualities.get(testEq);
					}
				}
			}
			// If no select equality could be found, return null.
			return null;
		}

		/**
		 * Close the outer paths which are still open at the left or right end. There is nothing to do in the cases
		 * where we don't have a shared index, because if there was an A-local outer path in the B-local case (or vice
		 * versa), it has already been closed by using either head- or tailOccur. For partitions where the main diseq is
		 * mixed, we have to close all the partitions on the way from mHead.mColor to mTail.mColor (except for their lca
		 * partition). For partitions where the main diseq is A(resp. B)-local or shared and a shared select index
		 * exists, B(resp. A)-local and mixed index diseqs on outer A(resp. B)-paths have to be added to the interpolant
		 * as premise (resp. conjunct). Note that this uses the recursionVar for closing index paths of mixed weakeq-ext
		 * lemmas.
		 */
		private void closeWeakPath() {
			// TODO closeWeakPath() and closeWeakeqExt() should be improved

			// First, close the paths in partitions where the main diseq is mixed, or where it is shared and one of the
			// outer paths is in A and the other one in B => select equalities are built.
			while (mHead.mColor < mNumInterpolants || mTail.mColor < mNumInterpolants) {
				if (mHead.mColor < mTail.mColor) { // the left outer path is an A-path
					final int color = mHead.mColor;
					// Add the interpolant for the left (A) path
					mHead.addInterpolantClauseOuterAPath(color);
					// Add the interpolant for the right (B) path, i.e. the A part of index diseqs
					mTail.addInterpolantClauseOuterBPath(color);
					// go to the parent partition
					mHead.mColor = getParent(mHead.mColor);
				} else if (mHead.mColor == mTail.mColor) {
					// The whole path is in A
					mHead.addInterpolantClauseOuterAPath(mHead.mColor);
					mHead.mColor = mTail.mColor = getParent(mHead.mColor);
				} else { // the right outer path is an A-path
					final int color = mTail.mColor;
					// Add the interpolant for the right (A) path
					mTail.addInterpolantClauseOuterAPath(color);
					// Add the interpolant for the left (B) path, i.e. the A part of index diseqs
					mHead.addInterpolantClauseOuterBPath(color);
					// go to the parent partition
					mTail.mColor = getParent(mTail.mColor);
				}
			}
			// Then, close the paths for partitions where the outer open paths and the main diseq are all in A (or B).
			// Here, only index disequalities are added.
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mSharedIndex[color] == null) { // Nothing to do in the cases where no shared select index exists.
					continue;
				}
				if (mHead.mIndexDiseqs[color] == null && mTail.mIndexDiseqs[color] == null
						&& mHead.mIndexEqs[color] == null && mTail.mIndexEqs[color] == null) { // No FPiA/ FPiB
					continue;
				}
				final Term index = mSharedIndex[color];
				final Map<ApplicationTerm, LitInfo> allDiseqs = new HashMap<ApplicationTerm, LitInfo>();
				final Map<ApplicationTerm, LitInfo> allEqs = new HashMap<ApplicationTerm, LitInfo>();
				if (mHead.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mHead.mIndexDiseqs[color]);
				}
				if (mHead.mIndexEqs[color] != null) {
					allEqs.putAll(mHead.mIndexEqs[color]);
				}
				if (mTail.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mTail.mIndexDiseqs[color]);
				}
				if (mTail.mIndexEqs[color] != null) {
					allEqs.putAll(mTail.mIndexEqs[color]);
				}
				if (mDiseqInfo.isALocal(color)) {
					// A-local outer paths must be closed, B-local ones are already apart from the shared case.
					assert mHead.mTerm[color] != null || mTail.mTerm[color] != null; // one of the outer paths is in A
					// Add the B part of the diseqs as premise for the interpolant
					final Term fPiA = buildFPiATerm(color, index, allDiseqs, allEqs);
					mPathInterpolants[color].add(fPiA);

					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
					mHead.mIndexEqs[color] = mTail.mIndexEqs[color] = null;
				} else {
					assert mDiseqInfo.isBorShared(color);
					// B-local paths must be closed, A-local ones are already closed, at the latest in the 1st part.
					assert mHead.mTerm[color] == null || mTail.mTerm[color] == null; // one of the outer paths is in B
					// Add the A part of the diseqs as conjunct to the interpolant
					final Term fPiB = buildFPiBTerm(color, index, allDiseqs, allEqs);
					mPathInterpolants[color].add(fPiB);
					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
					mHead.mIndexEqs[color] = mTail.mIndexEqs[color] = null;
				}
			}
		}

		/**
		 * Close the store path of an extensionality lemma. This includes building the recursive interpolant for the
		 * mixed case.
		 *
		 * @param headOcc
		 *            the occurrence of the left store path end
		 * @param tailOcc
		 *            the occurrence of the right store path end
		 */
		private void closeWeakeqExt(final Occurrence headOcc, final Occurrence tailOcc) {
			// First, close the paths in partitions where the main diseq is shared and one of the outer paths is in A
			// and the other one in B. In this case, mLastChange[color] != null.
			while (mHead.mColor < mNumInterpolants || mTail.mColor < mNumInterpolants) {
				if (mHead.mColor < mTail.mColor) { // the left outer path is an A-path
					final int color = mHead.mColor;
					if (!mDiseqInfo.isMixed(color)) {
						// Add the interpolant for the left (A) path
						mHead.addInterpolantClauseAPathExt(color, mPath[0]);
						// Add the interpolant for the right (B) path, i.e. the A part of index diseqs
						mTail.addInterpolantClauseBPathExt(color, null);
					}
					// go to the parent partition
					mHead.mColor = getParent(mHead.mColor);
				} else if (mHead.mColor == mTail.mColor) {
					mTail.addInterpolantClauseAPathExt(mHead.mColor, mPath[mPath.length - 1]);
					mHead.mColor = mTail.mColor = getParent(mHead.mColor);
				} else { // the right outer path is an A-path
					final int color = mTail.mColor;
					if (!mDiseqInfo.isMixed(color)) {
						// Add the interpolant for the right (A) path
						mTail.addInterpolantClauseAPathExt(color, mPath[mPath.length - 1]);
						// Add the interpolant for the left (B) path, i.e. the A part of index diseqs
						mHead.addInterpolantClauseBPathExt(color, null);
					}
					// go to the parent partition
					mTail.mColor = getParent(mTail.mColor);
				}
			}
			// Then, close the other outer paths, and in the mixed case, build the recursive interpolant.
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mDiseqInfo.isALocal(color) || mDiseqInfo.isBorShared(color)) {
					if (mHead.mStoreIndices[color] == null && mTail.mStoreIndices[color] == null) {
						continue; // No subinterpolants.
					}
				}
				// Close the paths for partitions where the outer open paths and the main diseq are all in A (or B).
				// Here, only subinterpolants are added.
				if (mDiseqInfo.isALocal(color)) {
					// A-local outer paths must be closed here, B-local ones are already closed.
					mHead.addInterpolantClauseAPathExt(color, null);
					mTail.addInterpolantClauseAPathExt(color, null);
				} else if (mDiseqInfo.isBorShared(color)) {
					// B-local paths must be closed, A-local ones are already closed.
					mHead.addInterpolantClauseBPathExt(color, null);
					mTail.addInterpolantClauseBPathExt(color, null);
				} else { // Close one of the outer paths as before, and compute the recursive interpolant for the other.
					// Note: We cannot use addInterpolantClauseA/BPathExt here, as it clears mStoreIndices, which we
					// need for recursion
					if (headOcc.isALocal(color)) {
						if (mIsBInterpolated[color]) {
							if (mTail.mStoreIndices[color] != null) { // Holds when we use determineRecursionSide();
								for (final Term index : mTail.mStoreIndices[color]) {
									mPathInterpolants[color].add(mTail.calculateSubInterpolantBPath(index, null));
								}
							}
							mHead.buildRecursiveInterpolantAPath(color, mTail);
						} else {
							if (mHead.mStoreIndices[color] != null) { // Holds when we use determineRecursionSide();
								for (final Term index : mHead.mStoreIndices[color]) {
									mPathInterpolants[color].add(mHead.calculateSubInterpolantAPath(index, null));
								}
							}
							mTail.buildRecursiveInterpolantBPath(color, mHead);
						}
					} else {
						if (mIsBInterpolated[color]) {
							if (mHead.mStoreIndices[color] != null) { // Holds when we use determineRecursionSide();
								for (final Term index : mHead.mStoreIndices[color]) {
									mPathInterpolants[color].add(mHead.calculateSubInterpolantBPath(index, null));
								}
							}
							mTail.buildRecursiveInterpolantAPath(color, mHead);
						} else {
							if (mTail.mStoreIndices[color] != null) { // Holds when we use determineRecursionSide();
								for (final Term index : mTail.mStoreIndices[color]) {
									mPathInterpolants[color].add(mTail.calculateSubInterpolantAPath(index, null));
								}
							}
							mHead.buildRecursiveInterpolantBPath(color, mTail);
						}
					}
				}
			}
		}

		/**
		 * Build the F_pi^A - term. It collects the B-parts of index (dis)equalities on an A-path.
		 *
		 * @param color
		 *            the current partition
		 * @param sharedIndex
		 *            the shared term representing the weakpathindex
		 * @param indexDiseqs
		 *            disequalities between weakpathindex and indices of stores on the A-path
		 * @param indexEqs
		 *            equalities between weakpathindex and indices of select eqs on the A-path
		 * @return the disjunction of the negated B-parts of index diseqs on an A-path, in shared terms.
		 */
		private Term buildFPiATerm(final int color, final Term sharedIndex,
				final Map<ApplicationTerm, LitInfo> indexDiseqs, final Map<ApplicationTerm, LitInfo> indexEqs) {
			if (indexDiseqs == null && indexEqs == null) {
				return mTheory.mFalse;
			}
			final Set<Term> indexTerms = new HashSet<Term>();
			if (indexDiseqs != null) {
				for (final ApplicationTerm diseq : indexDiseqs.keySet()) {
					final LitInfo info = indexDiseqs.get(diseq);
					// Index diseqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the store index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: diseq.getParameters()[0].equals(mPathIndex) ? diseq.getParameters()[1]
									: diseq.getParameters()[0];
					indexTerms.add(mTheory.equals(index, sharedIndex));
				}
			}
			if (indexEqs != null) {
				for (final ApplicationTerm eq : indexEqs.keySet()) {
					final LitInfo info = indexEqs.get(eq);
					// Index eqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the select index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: eq.getParameters()[0].equals(mPathIndex) ? eq.getParameters()[1] : eq.getParameters()[0];
					indexTerms.add(mTheory.not(mTheory.equals(index, sharedIndex)));
				}
			}
			final Term fATerm = mTheory.or(indexTerms.toArray(new Term[indexTerms.size()]));
			return fATerm;
		}

		/**
		 * Build the F_pi^B - term. It collects the A-parts of index (dis)equalities on a B-path.
		 *
		 * @param color
		 *            the current partition
		 * @param sharedIndex
		 *            the shared term representing the weakpathindex
		 * @param indexDiseqs
		 *            disequalities between weakpathindex and indices of stores on the B-path
		 * @param indexEqs
		 *            equalities between weakpathindex and indices of select eqs on the B-path
		 * @return the conjunction of the A-parts of index diseqs on a B-path, in shared terms.
		 */
		private Term buildFPiBTerm(final int color, final Term sharedIndex,
				final Map<ApplicationTerm, LitInfo> indexDiseqs, final Map<ApplicationTerm, LitInfo> indexEqs) {
			if (indexDiseqs == null && indexEqs == null) {
				return mTheory.mTrue;
			}
			final Set<Term> indexTerms = new HashSet<Term>();
			if (indexDiseqs != null) {
				for (final ApplicationTerm diseq : indexDiseqs.keySet()) {
					final LitInfo info = indexDiseqs.get(diseq);
					// Index diseqs are either mixed or A-local.
					// In the first case, there is a mixed term, in the second, the store index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: diseq.getParameters()[0].equals(mPathIndex) ? diseq.getParameters()[1]
									: diseq.getParameters()[0];
					if (info.isMixed(color)) { // Add the A projection of the index diseq (an eq in the mixed case)
						indexTerms.add(mTheory.equals(index, sharedIndex));
					} else if (info.isALocal(color)) {
						// If the index diseq is A local, the A projection is the diseq itself.
						indexTerms.add(mTheory.not(mTheory.equals(index, sharedIndex)));
					}
				}
			}
			if (indexEqs != null) {
				for (final ApplicationTerm eq : indexEqs.keySet()) {
					final LitInfo info = indexEqs.get(eq);
					// Index eqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the select index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: eq.getParameters()[0].equals(mPathIndex) ? eq.getParameters()[1] : eq.getParameters()[0];
					indexTerms.add(mTheory.equals(index, sharedIndex));
				}
			}
			final Term fBTerm = mTheory.and(indexTerms.toArray(new Term[indexTerms.size()]));
			return fBTerm;
		}

		/**
		 * To interpolate a weak path, we iterate over the equality and store steps on the weak path. The WeakPathEnd
		 * collects the information that has to be processed between this weak path end and the current position.
		 */
		class WeakPathEnd {
			/**
			 * The first partition for which there is an A-local prefix of the path. If mHasABPath is non-empty, this is
			 * the first partition that is not in mHasABPath, i.e. the first for which only a continuous A-path but not
			 * a continuous B-path exists.
			 */
			int mColor;
			/**
			 * For each partition this contains the term that ends the first A-local chain of equalities. Note that
			 * mTerm[color] is distinct from null only for paths which are still open on the opposite end.
			 */
			Term[] mTerm;
			/**
			 * For each partition, this contains the term which marks the last change from A to B or vice versa. This
			 * can be the same term as in mTerm if the path is A local and still open on the opposite side.
			 */
			Term[] mLastChange;
			/**
			 * For each partition this contains the set of B(resp. A)-local and mixed store index disequalities found on
			 * the A (resp. B) path so far.
			 */
			Map<ApplicationTerm, LitInfo>[] mIndexDiseqs;
			/**
			 * For each partition this contains the set of B(resp. A)-local and mixed select index equalities found on
			 * the A (resp. B) path so far.
			 */
			Map<ApplicationTerm, LitInfo>[] mIndexEqs;
			/**
			 * For each partition, this stores the store indices on the A (B) path so far. This is only used for the
			 * main path of a weakeq-ext lemma.
			 */
			Set<Term>[] mStoreIndices;

			@SuppressWarnings("unchecked")
			public WeakPathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
				mLastChange = new Term[mNumInterpolants];
				if (mPathIndex != null) {
					mIndexDiseqs = new Map[mNumInterpolants];
					mIndexEqs = new Map[mNumInterpolants];
				} else { // the path is the store path of a weakeq-ext lemma
					mStoreIndices = new Set[mNumInterpolants];
				}
			}

			/**
			 * Close A paths in all partitions where we are on an A path and we add a term that is B-local for this
			 * partition. This opens B-paths at the same time.
			 *
			 * @param other
			 *            the other path end
			 * @param boundary
			 *            the boundary term for opening/closing the path
			 * @param occur
			 *            the occurrence of the literal containing the boundary term
			 */
			public void closeAPath(final WeakPathEnd other, final Term boundary, final Occurrence occur) {
				assert other.mColor <= mMaxColor;
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					closeSingleAPath(other, boundary);
				}
			}

			/**
			 * Open A paths in all partitions where we are on a B path and we add a term that is A-local for this
			 * partition. This closes B-paths at the same time.
			 *
			 * @param other
			 *            the other path end
			 * @param boundary
			 *            the boundary term for opening/closing the path
			 * @param occur
			 *            the occurrence of the literal containing the boundary term
			 */
			public void openAPath(final WeakPathEnd other, final Term boundary, final Occurrence occur) {
				while (true) {
					final int child = getChild(mColor, occur);
					// if there is no A-local child, we are done.
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					openSingleAPath(other, boundary, child);
				}
			}

			/**
			 * Close the A path for partition color. This is called when we add a term to the chain that is B-local for
			 * the current mColor. We set mColor to the parent node. We also close the open path on mColor or open a new
			 * one and increment mMaxColor if such a path was not yet open. Note that closing an A path opens a B path
			 * at the same time.
			 *
			 * @param other
			 *            the other PathEnd
			 * @param boundary
			 *            the boundary term for opening/closing the path.
			 */
			private void closeSingleAPath(final WeakPathEnd other, final Term boundary) {
				// This should be empty now, since we anded it with occur.mInA and the occurrence is not in A for color.
				assert mHasABPath.isEmpty();
				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) { // the path is already closed at the left side by a B path in front of it
					// Add the interpolant clause for this A path.
					if (mPathIndex != null) {
						addInterpolantClauseAPath(color, boundary);
					} else { // Store path in weakeq-ext lemma
						addInterpolantClauseAPathExt(color, boundary);
					}
					mTerm[color] = null;
				} else {
					assert mMaxColor == color;
					other.mTerm[color] = boundary;
					mMaxColor = getParent(color);
				}
				mLastChange[color] = boundary;
				if (other.mLastChange[color] == null) {
					other.mLastChange[color] = boundary;
				}
			}

			/**
			 * Open a new A path. This is called when a term is added that is A local in child, where child is a child
			 * of mColor. We start a new A path on child. If we have still slack, since mHasABPath contains child, we
			 * don't have to open the path and just set mMaxColor to child. Note that opening an A path closes a B path
			 * at the same time.
			 *
			 * @param other
			 *            the other path end.
			 * @param boundary
			 *            the term that starts the new A path.
			 * @param child
			 *            the child of mColor for which the added term is A local.
			 */
			private void openSingleAPath(final WeakPathEnd other, final Term boundary, final int child) {
				if (mHasABPath.get(child)) {
					mMaxColor = other.mColor = mColor = child;
					// Compute all nodes below child excluding child itself
					final BitSet subtree = new BitSet();
					subtree.set(mInterpolator.mStartOfSubtrees[child], child);
					// Keep only those below the current child.
					mHasABPath.and(subtree);
				} else {
					// Open a new A path.
					mTerm[child] = boundary;
					mColor = child;
					// Add an interpolant clause for partitions where this closes a B path
					if (mLastChange[child] != null) {
						if (mPathIndex != null) {
							addInterpolantClauseBPath(child, boundary);
						} else { // we are on the store path in a weakeq-ext lemma
							addInterpolantClauseBPathExt(child, boundary);
						}
					}
					mLastChange[child] = boundary;
					if (other.mLastChange[child] == null) {
						other.mLastChange[child] = boundary;
					}
					mHasABPath.clear();
				}
			}

			/**
			 * Add the disequality between the weakpath index and a store index. There are three cases where it has to
			 * be included in the interpolant: (i) the disequality is mixed, (ii) the disequality is A local on a B
			 * local path segment, (iii) the disequality is B local on an A local path segment.
			 *
			 * @param other
			 *            The other path end.
			 * @param storeTerm
			 *            The store term from which we extract the store index.
			 */
			private void addIndexDisequality(final WeakPathEnd other, final Term storeTerm) {
				assert isStoreTerm(storeTerm);
				final Term storeIndex = getIndexFromStore(storeTerm);
				final ApplicationTerm diseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
				final LitInfo diseqInfo = mInterpolator.getLiteralInfo(diseq);

				// The diseq has to be added to all partitions where it is mixed and all partitions that lie on the
				// tree path between the partition of the diseq and the partition of the store term.
				// In nodes under the lca which are not on the way, both are in B, in nodes above the lca both are in A,
				// and in both cases there is nothing to do.
				addIndexDiseqAllColors(other, diseqInfo, diseq, diseqInfo);
				if (diseqInfo.getMixedVar() != null) {
					// additionally go up and down with weakpathindexoccur
					final Occurrence occur = mInterpolator.getOccurrence(mPathIndex, null);
					addIndexDiseqAllColors(other, occur, diseq, diseqInfo);
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index disequality to
			 * those partitions. This adds the index disequality to all partitions where it is not in A (resp. B) while
			 * the path is.
			 */
			private void addIndexDiseqAllColors(final WeakPathEnd other, final Occurrence occur,
					final ApplicationTerm diseq, final LitInfo diseqInfo) {
				int currentColor = mColor;
				// Up
				mHasABPath.and(occur.mInA);
				while (currentColor < mNumInterpolants && occur.isBLocal(currentColor)) {
					assert mHasABPath.isEmpty();
					final int color = currentColor;
					currentColor = getParent(color);
					addIndexDiseqOneColor(other, diseq, diseqInfo, color);
				}
				// Down
				while (true) {
					final int child = getChild(currentColor, occur);
					// If there is no A-local child, we are done.
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					if (mHasABPath.get(child)) {
						// Compute all nodes below child excluding child itself
						final BitSet subtree = new BitSet();
						subtree.set(mInterpolator.mStartOfSubtrees[child], child);
						// Keep only those below the current child.
						mHasABPath.and(subtree);
					} else {
						addIndexDiseqOneColor(other, diseq, diseqInfo, child);
						currentColor = child;
					}
				}
			}

			/**
			 * Add the index disequality to one partition.
			 */
			private void addIndexDiseqOneColor(final WeakPathEnd other, final ApplicationTerm diseq,
					final LitInfo diseqInfo, final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexDiseqs[color] == null) {
						other.mIndexDiseqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					other.mIndexDiseqs[color].put(diseq, diseqInfo);
				} else { // else in this one.
					if (mIndexDiseqs[color] == null) {
						mIndexDiseqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					mIndexDiseqs[color].put(diseq, diseqInfo);
				}
			}

			/**
			 * Add the equality between the weakpath index and a select index. There are three cases where it has to be
			 * included in the interpolant: (i) the equality is mixed, (ii) the equality is A local on a B local path
			 * segment, (iii) the equality is B local on an A local path segment.
			 *
			 * @param other
			 *            The other path end.
			 * @param selectTerm
			 *            The select term from which we extract the select index.
			 */
			private void addSelectIndexEquality(final WeakPathEnd other, final Term selectTerm) {
				assert isSelectTerm(selectTerm);
				if (getIndexFromSelect(selectTerm) != mPathIndex) {
					final Term selectIndex = getIndexFromSelect(selectTerm);
					final ApplicationTerm indexEq = mEqualities.get(new SymmetricPair<Term>(selectIndex, mPathIndex));
					final LitInfo eqInfo = mInterpolator.getLiteralInfo(indexEq);
					addSelectIndexEqAllColors(other, eqInfo, indexEq, eqInfo);
					if (eqInfo.getMixedVar() != null) {
						final Occurrence occur = mInterpolator.getOccurrence(mPathIndex, null);
						addSelectIndexEqAllColors(other, occur, indexEq, eqInfo);
					}
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index equality to
			 * those partitions. This adds the index equality to all partitions where it is not in A (resp. B) while the
			 * path is.
			 */
			private void addSelectIndexEqAllColors(final WeakPathEnd other, final Occurrence occur,
					final ApplicationTerm eq, final LitInfo eqInfo) {
				int currentColor = mColor;
				// Up
				mHasABPath.and(occur.mInA);
				while (currentColor < mNumInterpolants && occur.isBLocal(currentColor)) {
					assert mHasABPath.isEmpty();
					final int color = currentColor;
					currentColor = getParent(color);
					addSelectIndexEqOneColor(other, eq, eqInfo, color);
				}
				// Down
				while (true) {
					final int child = getChild(currentColor, occur);
					// If there is no A-local child, we are done.
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					if (mHasABPath.get(child)) {
						// Compute all nodes below child excluding child itself
						final BitSet subtree = new BitSet();
						subtree.set(mInterpolator.mStartOfSubtrees[child], child);
						// Keep only those below the current child.
						mHasABPath.and(subtree);
					} else {
						addSelectIndexEqOneColor(other, eq, eqInfo, child);
						currentColor = child;
					}
				}
			}

			/**
			 * Add the index equality to one partition.
			 */
			private void addSelectIndexEqOneColor(final WeakPathEnd other, final ApplicationTerm eq,
					final LitInfo eqInfo, final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexEqs[color] == null) {
						other.mIndexEqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					other.mIndexEqs[color].put(eq, eqInfo);
				} else { // else in this one.
					if (mIndexEqs[color] == null) {
						mIndexEqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					mIndexEqs[color].put(eq, eqInfo);
				}
			}

			/**
			 * Add an interpolant clause for a closed A path. Case (i) (shared select index and mDiseq not A-local): the
			 * conjunction of all B-local or the B-part of mixed index diseqs on this path is a premise for the arrays
			 * at the path ends to coincide at weakpathindex => interpolant conjunct of the form
			 * "i!=k1/\.../\i!=kn->start[i]=end[i]". Case (ii) (shared select index and mDiseq A-local): B-local index
			 * diseqs are a premise for all interpolant parts summarizing A paths. Case (iii) (mDiseq B-local, no shared
			 * select index): Summarize the path by a WEQ term stating that the arrays at the path end differ at most at
			 * k locations (k= # of B-local and mixed index diseqs on the path) which are all different from
			 * weakpathindex. Case (iv) (mDiseq A-local, no shared select index): Nothing to do.
			 */
			private void addInterpolantClauseAPath(final int color, final Term boundary) {
				final Term left = mLastChange[color];
				final Term right = boundary;
				if (mSharedIndex[color] != null) {
					if (!mIsBInterpolated[color]) { // Case (ii)
						assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
						if (mIndexDiseqs[color] != null) {
							assert mSharedIndex[color] == mPathIndex;
							final Term fPiA =
									buildFPiATerm(color, mSharedIndex[color], mIndexDiseqs[color], mIndexEqs[color]);
							mPathInterpolants[color].add(fPiA);
							mIndexDiseqs[color] = null;
							mIndexEqs[color] = null;
						}
					} else { // Case (i)
						final Term index = mSharedIndex[color];
						final Term fPiA = buildFPiATerm(color, index, mIndexDiseqs[color], mIndexEqs[color]);
						final Term selectEq = buildSelectEq(left, right, index);
						final Term itpClause = mTheory.or(selectEq, fPiA);
						mPathInterpolants[color].add(itpClause);
						mIndexDiseqs[color] = null;
						mIndexEqs[color] = null;
					}
				} else if (!mIsBInterpolated[color]) { // Case (iv)
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					assert mIndexDiseqs[color] == null;
					return;
				} else { // Case (iii)
					assert mIsBInterpolated[color];
					assert mDiseqInfo.isBLocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					final Term fPiA = buildFPiATerm(color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
					final Term itpClause = buildWeqTerm(left, right, order, fPiA, cdot);
					mPathInterpolants[color].add(itpClause);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
				}
			}

			/**
			 * Add an interpolant clause for a closed B path. Case (i) (shared select index, mDiseq not A-local):
			 * A-local and the A part of mixed index disequalities are added as conjunct to the entire lemma
			 * interpolant. Case (ii) (shared select index, mDiseq A-local): Summarize the path by stating that the
			 * arrays at the path ends differ at weakpathindex => interpolant disjunct of the form
			 * "i!=k1/\.../\i!=kn/\start[i]!=end[i]". Case (iii) (B-local, no shared select index): Nothing to do. Case
			 * (iv) (A-local, no shared select index): Summarize the path by an NWEQ term stating that the arrays at the
			 * path end differ at least at k locations (k= # B-local and mixed index diseqs on the path) of which (at
			 * least) one equals the weakpathindex.
			 */
			private void addInterpolantClauseBPath(final int color, final Term boundary) {
				final Term left = mLastChange[color];
				final Term right = boundary;
				Term fPiB = mTheory.mTrue;
				if (mSharedIndex[color] != null) {
					final Term index = mSharedIndex[color];
					if (mIndexDiseqs[color] != null) {
						fPiB = buildFPiBTerm(color, index, mIndexDiseqs[color], mIndexEqs[color]);
					}
					if (!mIsBInterpolated[color]) { // Case (ii)
						assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext"); // TEST
						final Term selectDiseq = mTheory.not(buildSelectEq(left, right, index));
						final Term itpClause = mTheory.and(selectDiseq, fPiB);
						mPathInterpolants[color].add(itpClause);
					} else { // Case (i)
						mPathInterpolants[color].add(fPiB);
					}
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
				} else if (!mIsBInterpolated[color]) { // Case (iv)
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					fPiB = buildFPiBTerm(color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
					final Term itpClause = buildNweqTerm(left, right, order, fPiB, cdot);
					mPathInterpolants[color].add(itpClause);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
				} else { // Case (iii)
					assert mIsBInterpolated[color];
					assert mDiseqInfo.isBLocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					assert mIndexDiseqs[color] == null;
					return;
				}
			}

			/**
			 * Add an interpolant clause for a closed A path on the main path of weakeq-ext. If mDiseq is in B, or we
			 * build the recursive interpolant in a mixed lemma based on the B-interpolant, this builds weq-terms that
			 * include interpolant terms for the index paths of the store indices. Else, it just adds interpolant terms
			 * for the index paths.
			 *
			 * @param color
			 *            The current partition
			 * @param boundary
			 *            The term that closes this A path
			 */
			void addInterpolantClauseAPathExt(final int color, final Term boundary) {
				// Store the inner paths on the main path for mixed weakeq-ext lemmas
				if (mDiseqInfo.isMixed(color) && mLastChange[mColor] != null) {
					if (boundary != mPath[0] && boundary != mPath[mPath.length - 1]) {
						final int order = mStoreIndices[color] == null ? 0 : mStoreIndices[color].size();
						mInnerPaths[color].put(new SymmetricPair<Term>(mLastChange[color], boundary), order);
					}
				}
				// Add interpolant clauses
				if (!mIsBInterpolated[color]) {
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext"); // TEST
					if (mStoreIndices[color] != null) {
						for (final Term index : mStoreIndices[color]) {
							mPathInterpolants[color].add(calculateSubInterpolantAPath(index, null));
						}
					}
				} else {
					assert mDiseqInfo.isBorShared(color) || mDiseqInfo.isMixed(color); // TEST
					final Term left = mLastChange[color];
					assert left != null;
					final Term right = boundary;
					if (mStoreIndices[color] != null) {
						int order = 0;
						Term formula = mTheory.mFalse;
						final TermVariable doubledot = mTheory.createFreshTermVariable("doubledot",
								mStoreIndices[color].iterator().next().getSort());
						order = mStoreIndices[color].size();
						final Set<Term> subInterpolants = new HashSet<Term>();
						for (final Term index : mStoreIndices[color]) {
							subInterpolants.add(calculateSubInterpolantAPath(index, doubledot));
						}
						formula = mTheory.or(subInterpolants.toArray(new Term[subInterpolants.size()]));
						final Term weqTerm = buildWeqTerm(left, right, order, formula, doubledot);
						mPathInterpolants[color].add(weqTerm);
					} else {
						mPathInterpolants[color].add(mTheory.equals(left, right));
					}
				}
				mStoreIndices[color] = null;
			}

			/**
			 * Add an interpolant clause for a closed B path on the main path of weakeq-ext. If mDiseq is in A, or we
			 * build the recursive interpolant in a mixed lemma based on the A-interpolant, this builds nweq-terms that
			 * include interpolant terms for the index paths of the store indices. Else, it just adds interpolant terms
			 * for the index paths.
			 *
			 * @param color
			 *            The current partition
			 * @param boundary
			 *            The term that closes this A path
			 */
			void addInterpolantClauseBPathExt(final int color, final Term boundary) {
				// Store the inner paths on the main path for mixed weakeq-ext lemmas
				if (mDiseqInfo.isMixed(color) && mLastChange[mColor] != null) {
					if (boundary != mPath[0] && boundary != mPath[mPath.length - 1]) {
						final int order = mStoreIndices[color] == null ? 0 : mStoreIndices[color].size();
						mInnerPaths[color].put(new SymmetricPair<Term>(mLastChange[color], boundary), order);
					}
				}
				// Add interpolant clauses
				if (mIsBInterpolated[color]) {
					assert mDiseqInfo.isBorShared(color) || mDiseqInfo.isMixed(color); // TEST
					if (mStoreIndices[color] != null) {
						for (final Term index : mStoreIndices[color]) {
							mPathInterpolants[color].add(calculateSubInterpolantBPath(index, null));
						}
					}
				} else if (!mIsBInterpolated[color]) {
					assert mDiseqInfo.isALocal(color) || mDiseqInfo.isMixed(color); // TEST
					final Term left = mLastChange[color];
					assert left != null;
					final Term right = boundary;
					if (mStoreIndices[color] != null) {
						int order = 0;
						Term formula = mTheory.mFalse;
						final TermVariable doubledot = mTheory.createFreshTermVariable("doubledot",
								mStoreIndices[color].iterator().next().getSort());
						order = mStoreIndices[color].size();
						final Set<Term> subInterpolants = new HashSet<Term>();
						for (final Term index : mStoreIndices[color]) {
							subInterpolants.add(calculateSubInterpolantBPath(index, doubledot));
						}
						formula = mTheory.and(subInterpolants.toArray(new Term[mPathInterpolants[color].size()]));
						final Term nweqTerm = buildNweqTerm(left, right, order, formula, doubledot);
						mPathInterpolants[color].add(nweqTerm);
					} else {
						mPathInterpolants[color].add(mTheory.not(mTheory.equals(left, right)));
					}
				}
				mStoreIndices[color] = null;
			}

			/**
			 * Add the store index of a store step in the main path of weakeq-ext.
			 *
			 * @param other
			 *            the other path end
			 * @param storeTerm
			 *            the store term from which we extract the index
			 */
			private void addStoreIndex(final WeakPathEnd other, final Term storeTerm) {
				assert isStoreTerm(storeTerm);
				final Term storeIndex = getIndexFromStore(storeTerm);
				for (int color = 0; color < mNumInterpolants; color++) {
					// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null,
					// we have to store the diseq in the other pathend
					if (other.mLastChange[color] == null) {
						if (other.mStoreIndices[color] == null) {
							other.mStoreIndices[color] = new HashSet<Term>();
						}
						other.mStoreIndices[color].add(storeIndex);
					} else { // else in this one.
						if (mStoreIndices[color] == null) {
							mStoreIndices[color] = new HashSet<Term>();
						}
						mStoreIndices[color].add(storeIndex);
					}
				}
			}

			/**
			 * Calculate the sub-interpolant for an index on an A path in weakeq-ext lemmas.
			 *
			 * @param index
			 *            The path index
			 * @param auxIndex
			 *            The auxiliary variable representing the index that is used to include this subinterpolant in
			 *            an nweq term of the main path
			 * @return The path interpolant for the weakpath for weak congruence on index.
			 */
			private Term calculateSubInterpolantAPath(final Term index, final TermVariable auxIndex) {
				Term subInterpolant = mTheory.mFalse;
				final WeakPathInfo indexPath = new WeakPathInfo(mIndexPaths.get(index));

				mSharedIndex = new Term[mNumInterpolants];
				// Determine the shared term for the index
				for (int color = 0; color < mNumInterpolants; color++) {
					if (!mIsBInterpolated[color]) {
						assert mDiseqInfo.isALocal(color) || mDiseqInfo.isMixed(color);
						// in the A-local case, we look if there exists a shared index to decide whether we have to
						// build the select interpolant or the weq interpolant
						mSharedIndex[color] = findSharedTerm(index, color);
						subInterpolant = mTheory.or(indexPath.interpolateWeakPathInfo()[color]
								.toArray(new Term[mInterpolants[color].size()]));
					} else {
						assert mIsBInterpolated[color];
						assert mDiseqInfo.isBorShared(color) || mDiseqInfo.isMixed(color); // TEST
						// here, the subinterpolant gets the shared term auxVar
						mSharedIndex[color] = auxIndex;
						subInterpolant = mTheory.and(indexPath.interpolateWeakPathInfo()[color]
								.toArray(new Term[mInterpolants[color].size()]));
					}
				}
				return subInterpolant;
			}

			/**
			 * Calculate the subinterpolant for an index on a B path in weakeq-ext lemmas.
			 *
			 * @param index
			 *            The path index
			 * @param auxIndex
			 *            The auxiliary variable representing the index that is used to include this subinterpolant in
			 *            an nweq term of the main path
			 * @return The path interpolant for the weakpath for weak congruence on index.
			 */
			private Term calculateSubInterpolantBPath(final Term index, final TermVariable auxIndex) {
				Term subInterpolant = mTheory.mTrue;
				final WeakPathInfo indexPath = new WeakPathInfo(mIndexPaths.get(index));

				mSharedIndex = new Term[mNumInterpolants];
				// Determine the shared term for the index
				for (int color = 0; color < mNumInterpolants; color++) {
					if (!mIsBInterpolated[color]) {
						assert mDiseqInfo.isALocal(color) || mDiseqInfo.isMixed(color); // TEST
						// here, the subinterpolant gets the shared term auxVar
						mSharedIndex[color] = auxIndex;
						subInterpolant = mTheory.or(indexPath.interpolateWeakPathInfo()[color]
								.toArray(new Term[mInterpolants[color].size()]));
					} else {
						assert mIsBInterpolated[color];
						assert mDiseqInfo.isBorShared(color) || mDiseqInfo.isMixed(color); // TEST
						// in the A-local case, we look if there exists a shared index to decide whether we have to
						// build the select interpolant or the weq interpolant
						mSharedIndex[color] = findSharedTerm(index, color);
						subInterpolant = mTheory.and(indexPath.interpolateWeakPathInfo()[color]
								.toArray(new Term[mInterpolants[color].size()]));
					}
				}
				return subInterpolant;
			}

			/**
			 * Add an interpolant clause for an A path ending at the very left or very right path end. This is only used
			 * for partitions where the main disequality is mixed or shared. => interpolant conjunct of the form
			 * "i!=k1/\.../\i!=kn->start[i]=end[i]" Note that one needs the mixedVar here if mDiseqInfo.isMixed(color).
			 *
			 * @param color
			 *            the current partition
			 */
			private void addInterpolantClauseOuterAPath(final int color) {
				if (mSharedIndex[color] != null) {
					final Term index = mSharedIndex[color];
					final Term fPiA = buildFPiATerm(color, mSharedIndex[color], mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
					if (!mIsBInterpolated[color]) { // Case (ii)
						mPathInterpolants[color].add(fPiA);
					} else { // Case (i)
						final Term inner = mLastChange[color];
						final Term innerSelect, outerSelect;
						if (mDiseqInfo.isMixed(color)) {
							assert inner != null;
							if (inner instanceof ApplicationTerm && mEqualities.containsValue(inner)) {
								final LitInfo selectEq = mInterpolator.getLiteralInfo(inner);
								innerSelect = selectEq.getMixedVar();
							} else {
								innerSelect = mTheory.term("select", inner, index);
							}
							if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
								outerSelect = mDiseqInfo.getMixedVar();
							} else {
								outerSelect = mTheory.term("select", mRecursionVar, index);
							}
						} else { // The whole path from mPath[0] to mPath[mPath.length - 1] is A
							if (this.equals(mHead)) {
								innerSelect = mTheory.term("select", mPath[0], index);
								outerSelect = mTheory.term("select", mPath[mPath.length - 1], index);
							} else {
								innerSelect = mTheory.term("select", mPath[mPath.length - 1], index);
								outerSelect = mTheory.term("select", mPath[0], index);
							}
						}
						final Term selectEq = mTheory.equals(outerSelect, innerSelect);
						/*
						 * Here, we have to add the index equality if we are on a right outer A-path in the mixed case
						 * in read-over-weakeq and the index equality is B-local and both indices are shared.
						 */
						Term indexEq = mTheory.mFalse;
						if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
							if (this.equals(mTail) && mDiseqInfo.isMixed(color)) {
								final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
								if (indexEqInfo.isBLocal(color)) {
									final Term otherIndex =
											indexEqInfo.getMixedVar() != null ? indexEqInfo.getMixedVar()
													: mIndexEquality.getParameters()[0].equals(mPathIndex)
															? mIndexEquality.getParameters()[1]
															: mIndexEquality.getParameters()[0];
									final Occurrence otherIndexOccur = mInterpolator.getOccurrence(otherIndex, null);
									if (otherIndexOccur.isAB(color)) {
										indexEq = mTheory.not(mIndexEquality);
									}
								}
							}
						}
						final Term pre = mTheory.or(indexEq, fPiA);
						final Term itpClause = mTheory.or(pre, selectEq);
						mPathInterpolants[color].add(itpClause);
					}
				} else if (!mIsBInterpolated[color]) {
					assert mIndexDiseqs[color] == null;
				} else { // for outer paths, this should only happen in weakeq-ext lemmas.
					assert mLemmaInfo.getLemmaType().equals(":weakeq-ext") && mDiseqInfo.isMixed(color);
					final Term inner = mLastChange[color];
					final Term outer = mRecursionVar;
					assert mIndexEqs[color] == null;
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					final Term fPiA = buildFPiATerm(color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
					final Term itpClause = buildWeqTerm(inner, outer, order, fPiA, cdot);
					mPathInterpolants[color].add(itpClause);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
				}
			}

			/**
			 * Add an interpolant clause for a B path ending at the very left or very right path end.
			 *
			 * @param color
			 *            the current partition
			 */
			void addInterpolantClauseOuterBPath(final int color) {
				if (mSharedIndex[color] != null) {
					final Term index = mSharedIndex[color];
					final Term fPiB = buildFPiBTerm(color, index, mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
					if (mIsBInterpolated[color]) {
						mPathInterpolants[color].add(fPiB);
					} else { // This happens only in mixed weakeq-ext lemmas that are A-interpolated, i.e. as if diseq
								// was A-local.
						assert mDiseqInfo.isMixed(color); // If it is A-local, B paths are already closed
						// The path also must be closed on one side
						assert mLastChange[color] != null;
						final Term inner = mLastChange[color];
						final Term innerSelect;
						if (inner instanceof ApplicationTerm && mEqualities.containsValue(inner)) {
							final LitInfo selectEq = mInterpolator.getLiteralInfo(inner);
							innerSelect = selectEq.getMixedVar();
						} else {
							innerSelect = mTheory.term("select", inner, index);
						}
						assert mLemmaInfo.getLemmaType().equals(":weakeq-ext");
						final Term outerSelect = mTheory.term("select", mRecursionVar, index);
						final Term selectDiseq = mTheory.not(mTheory.equals(outerSelect, innerSelect));
						final Term itpClause = mTheory.and(selectDiseq, fPiB);
						mPathInterpolants[color].add(itpClause);
					}
				} else { // in mixed weakeq-ext, we can also have outer B paths with no shared index
					if (mLemmaInfo.getLemmaType().equals(":weakeq-ext") && mDiseqInfo.isMixed(color)) {
						assert mIndexEqs[color] == null;
						final Term inner = mLastChange[color];
						final Term outer = mRecursionVar;
						final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
						final Term fPiB = buildFPiBTerm(color, cdot, mIndexDiseqs[color], null);
						final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
						final Term itpClause = buildNweqTerm(outer, inner, order, fPiB, cdot);
						mPathInterpolants[color].add(itpClause);
					} else {
						assert mIndexDiseqs[color] == null;
					}
				}
			}

			/**
			 * Build the recursive weakeq-ext interpolant for mixed lemmas. The goal is to recursively build a shared
			 * term for the A-local path end from the array that closes this A path, by storing for each index the
			 * correct value which we can find in the corresponding index path.
			 *
			 * @param color
			 *            the current partition
			 * @param other
			 *            the other end of the store path
			 */
			void buildRecursiveInterpolantAPath(final int color, final WeakPathEnd other) {
				// Build the innermost interpolant term "mixedVar=recursionVar /\ B-Interpolant"
				final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), mRecursionVar);
				final Term bInterpolant =
						mTheory.and(mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				mPathInterpolants[color].clear();
				Term recursiveInterpolant = mTheory.and(eqTerm, bInterpolant);
				TermVariable lastRecVar = mRecursionVar;

				// Recursion over the store indices on this outer path
				for (final Term index : mStoreIndices[color]) {
					final TermVariable currentRecVar =
							mTheory.createFreshTermVariable("recursive", mRecursionVar.getSort());
					final WeakPathInfo indexPath = new WeakPathInfo(mIndexPaths.get(index));
					final Term rewriteAtIndex, rewriteToArray, rewriteWithElement;
					final Term pathInterpolant;
					// Check if there exists a shared term for the store index and interpolate the index path
					// accordingly
					final Term sharedIndex = findSharedTerm(index, color);
					if (sharedIndex != null) {
						rewriteAtIndex = sharedIndex;
						final Set<Term> recPathInterpolantTerms =
								indexPath.interpolateIndexPathForRecursion(sharedIndex, color);
						pathInterpolant =
								mTheory.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
						final Term lastChange = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
								: indexPath.mHead.mLastChange[color];
						if (lastChange instanceof ApplicationTerm && mEqualities.containsValue(lastChange)) {
							rewriteToArray = null;
							// Last change was at a mixed select equality
							final LitInfo selectEq = mInterpolator.getLiteralInfo(lastChange);
							rewriteWithElement = selectEq.getMixedVar();
						} else {
							rewriteToArray = lastChange;
							rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
						}
					} else {
						final TermVariable cdot = mTheory.createFreshTermVariable("cdot", index.getSort());
						rewriteAtIndex = cdot;
						final Set<Term> recPathInterpolantTerms =
								indexPath.interpolateIndexPathForRecursion(sharedIndex, color);
						pathInterpolant =
								mTheory.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
						final Term lastChange = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
								: indexPath.mHead.mLastChange[color];
						assert !(lastChange instanceof ApplicationTerm && mEqualities.containsValue(lastChange));
						rewriteToArray = lastChange;
						rewriteWithElement = mTheory.term("select", lastChange, rewriteAtIndex);
					}
					// Build the FPiBTerm for the outer B path of the index path
					final Term fPiB;
					// Needed for case without shared index (then there are no indexEqs)
					final int fPiBOrderForRecursion;
					if (this.equals(mHead)) { // The right outer path is the B path
						final Map<ApplicationTerm, LitInfo> indexDiseqs = indexPath.mTail.mIndexDiseqs[color];
						fPiBOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
						fPiB = buildFPiBTerm(color, rewriteAtIndex, indexDiseqs, indexPath.mTail.mIndexEqs[color]);
					} else { // The left outer path is the B path
						final Map<ApplicationTerm, LitInfo> indexDiseqs = indexPath.mHead.mIndexDiseqs[color];
						fPiBOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
						fPiB = buildFPiBTerm(color, rewriteAtIndex, indexDiseqs, indexPath.mHead.mIndexEqs[color]);
					}
					// Insert the rewritten term into the inner interpolant term
					final Term rewriteRecVar = mTheory.term("store", currentRecVar, rewriteAtIndex, rewriteWithElement);
					final Term rewriteRecInterpolant =
							mTheory.and(fPiB, mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant));
					// Build the final recursive interpolant
					if (sharedIndex != null) {
						recursiveInterpolant = mTheory.or(pathInterpolant, rewriteRecInterpolant);
					} else {
						assert rewriteAtIndex instanceof TermVariable;
						assert rewriteToArray != null;
						final TermVariable nweqDot = (TermVariable) rewriteAtIndex;
						final Set<Term> nweqTerms = new HashSet<Term>();
						// Build the nweq terms for all inner paths
						for (final SymmetricPair<Term> innerPath : mInnerPaths[color].keySet()) {
							final Term nweqTerm = buildNweqTerm(innerPath.getFirst(), innerPath.getSecond(),
									mInnerPaths[color].get(innerPath), rewriteRecInterpolant, nweqDot);
							nweqTerms.add(nweqTerm);
						}
						// Build the nweq term for the concatenation of the outer B-paths on store and index path
						final Term concatLeft = mLastChange[color];
						final Term concatRight = rewriteToArray;
						final Set<Term> otherMainStores = other.mStoreIndices[color];
						final int concatStores =
								fPiBOrderForRecursion + (otherMainStores == null ? 0 : otherMainStores.size());
						final Term concatNweqTerm =
								buildNweqTerm(concatLeft, concatRight, concatStores, rewriteRecInterpolant, nweqDot);
						nweqTerms.add(concatNweqTerm);
						final Term nweqPart = mTheory.or(nweqTerms.toArray(new Term[nweqTerms.size()]));
						recursiveInterpolant = mTheory.let(lastRecVar, currentRecVar, recursiveInterpolant);
						recursiveInterpolant = mTheory.or(recursiveInterpolant, pathInterpolant, nweqPart);
					}
					lastRecVar = currentRecVar;
				}
				// Replace the recursionVar by the first shared term
				recursiveInterpolant = mTheory.let(lastRecVar, mLastChange[color], recursiveInterpolant);
				mPathInterpolants[color].add(recursiveInterpolant);
			}

			/**
			 * Build the recursive weakeq-ext interpolant for mixed lemmas. The goal is to recursively build a shared
			 * term for the B-local path end from the array that closes this B path, by storing for each index the
			 * correct value which we can find in the corresponding index path.
			 *
			 * @param color
			 *            the current partition
			 * @param other
			 *            the other end of the store path
			 */
			void buildRecursiveInterpolantBPath(final int color, final WeakPathEnd other) {
				// Build the innermost interpolant term "mixedVar!=recursionVar \/ A-Interpolant"
				final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), mRecursionVar);
				final Term aInterpolant =
						mTheory.or(mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				mPathInterpolants[color].clear();
				Term recursiveInterpolant = mTheory.or(eqTerm, aInterpolant);
				TermVariable lastRecVar = mRecursionVar;

				// Recursion over the store indices on this outer path
				for (final Term index : mStoreIndices[color]) {
					final TermVariable currentRecVar =
							mTheory.createFreshTermVariable("recursive", mRecursionVar.getSort());
					final WeakPathInfo indexPath = new WeakPathInfo(mIndexPaths.get(index));
					final Term rewriteAtIndex, rewriteToArray, rewriteWithElement;
					final Term pathInterpolant;
					// Check if there exists a shared term for the store index and interpolate the index path
					// accordingly
					final Term sharedIndex = findSharedTerm(index, color);
					if (sharedIndex != null) {
						rewriteAtIndex = sharedIndex;
						final Set<Term> recPathInterpolantTerms =
								indexPath.interpolateIndexPathForRecursion(sharedIndex, color);
						pathInterpolant =
								mTheory.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
						final Term lastChange = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
								: indexPath.mHead.mLastChange[color];
						if (lastChange instanceof ApplicationTerm && mEqualities.containsValue(lastChange)) {
							rewriteToArray = null;
							// Last change was at a mixed select equality
							final LitInfo selectEq = mInterpolator.getLiteralInfo(lastChange);
							rewriteWithElement = selectEq.getMixedVar();
						} else {
							rewriteToArray = lastChange;
							rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
						}
					} else {
						final TermVariable cdot = mTheory.createFreshTermVariable("cdot", index.getSort());
						rewriteAtIndex = cdot;
						final Set<Term> recPathInterpolantTerms =
								indexPath.interpolateIndexPathForRecursion(sharedIndex, color);
						pathInterpolant =
								mTheory.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
						final Term lastChange = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
								: indexPath.mHead.mLastChange[color];
						assert !(lastChange instanceof ApplicationTerm && mEqualities.containsValue(lastChange));
						rewriteToArray = lastChange;
						rewriteWithElement = mTheory.term("select", lastChange, rewriteAtIndex);
					}
					// Build the FPiATerm for the outer A path of the index path
					final Term fPiA;
					final int fPiAOrder; // Needed for case without shared index (then there are no indexEqs)
					if (this.equals(mHead)) { // The right outer path is the B path
						fPiAOrder = indexPath.mTail.mIndexDiseqs[color] == null ? 0
								: indexPath.mTail.mIndexDiseqs[color].size();
						fPiA = buildFPiATerm(color, rewriteAtIndex, indexPath.mTail.mIndexDiseqs[color],
								indexPath.mTail.mIndexEqs[color]);
					} else { // The left outer path is the A path
						fPiAOrder = indexPath.mHead.mIndexDiseqs[color] == null ? 0
								: indexPath.mHead.mIndexDiseqs[color].size();
						fPiA = buildFPiATerm(color, rewriteAtIndex, indexPath.mHead.mIndexDiseqs[color],
								indexPath.mHead.mIndexEqs[color]);
					}
					// Insert the rewritten term into the inner interpolant term
					final Term rewriteRecVar = mTheory.term("store", currentRecVar, rewriteAtIndex, rewriteWithElement);
					final Term rewriteRecInterpolant =
							mTheory.or(fPiA, mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant));
					// Build the final recursive interpolant
					if (sharedIndex != null) {
						recursiveInterpolant = mTheory.and(pathInterpolant, rewriteRecInterpolant);
					} else {
						assert rewriteAtIndex instanceof TermVariable;
						assert rewriteToArray != null;
						final TermVariable weqDot = (TermVariable) rewriteAtIndex;
						final Set<Term> weqTerms = new HashSet<Term>();
						// Build the weq terms for all inner paths
						for (final SymmetricPair<Term> innerPath : mInnerPaths[color].keySet()) {
							final Term weqTerm = buildWeqTerm(innerPath.getFirst(), innerPath.getSecond(),
									mInnerPaths[color].get(innerPath), rewriteRecInterpolant, weqDot);
							weqTerms.add(weqTerm);
						}
						// Build the weq term for the concatenation of the outer B-paths on store and index path
						final Term concatLeft = mLastChange[color];
						final Term concatRight = rewriteToArray;
						final Set<Term> otherMainStores = other.mStoreIndices[color];
						final int concatStores = fPiAOrder + (otherMainStores == null ? 0 : otherMainStores.size());
						final Term concatWeqTerm =
								buildWeqTerm(concatLeft, concatRight, concatStores, rewriteRecInterpolant, weqDot);
						weqTerms.add(concatWeqTerm);
						final Term weqPart = mTheory.and(weqTerms.toArray(new Term[weqTerms.size()]));
						recursiveInterpolant = mTheory.let(lastRecVar, currentRecVar, recursiveInterpolant);
						recursiveInterpolant = mTheory.and(recursiveInterpolant, pathInterpolant, weqPart);
					}
					lastRecVar = currentRecVar;
				}
				// Replace the recursionVar by the first shared term
				recursiveInterpolant = mTheory.let(lastRecVar, mLastChange[color], recursiveInterpolant);
				mPathInterpolants[color].add(recursiveInterpolant);
			}
		}
	}
}
