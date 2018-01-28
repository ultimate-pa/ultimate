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
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
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

	// TODO Avoid A- and B-specific methods.

	/* General info to set up the ArrayInterpolator */
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	private Set<Term>[] mInterpolants;

	/* Information for array lemmas */
	/**
	 * Information about the lemma proof term.
	 */
	private InterpolatorClauseTermInfo mLemmaInfo;
	/**
	 * The main disequality of this lemma, i.e., "a[i]!=b[j]" for read-over-weakeq lemmas or "a!=b" for weakeq-ext.
	 */
	private AnnotatedTerm mDiseq;
	/**
	 * The LitInfo for the main disequality of this lemma.
	 */
	private LitInfo mDiseqInfo;
	/**
	 * The atoms of the equality literals in this lemma. Note that they appear negated in the lemma clause.
	 */
	private Map<SymmetricPair<Term>, AnnotatedTerm> mEqualities;
	/**
	 * The atoms of the disequality literals in this lemma. Note that they appear positively in the lemma clause.
	 */
	private Map<SymmetricPair<Term>, AnnotatedTerm> mDisequalities;
	/**
	 * The store path between the arrays of the main disequality for weak equivalence in a weakeq-ext lemma, and for
	 * weak equivalence modulo i, where i is the path index, in a read-over-weakeq lemma.
	 */
	private ProofPath mStorePath;
	/**
	 * This determines in which way we build the interpolant. In A-local partitions, we summarize B-paths, in the
	 * B-local partitions A-paths. For read-over-weakeq, the partitions where mDiseq is A-local are A, all others are B.
	 * For weakext, if there exist mixed partitions, there is one where the outer A-path is strictly longer than the
	 * outer B-path, and then we want to build the recursion on the B-path. All partitions above this partition are in
	 * A. This occurrence has NO shared partitions.
	 */
	private Occurrence mABSwitchOccur;

	/* Specific information for read-over-weakeq-lemmas */
	/**
	 * The strong path between the select indices of the main disequality.
	 */
	private AnnotatedTerm mIndexEquality;

	/* Specific information for weakeq-ext-lemmas */
	/**
	 * This map contains the paths for weak congruence on index i.
	 */
	private Map<Term, ProofPath> mIndexPaths;
	/**
	 * Index paths that have already been interpolated.
	 */
	private Map<Term, WeakPathInfo> mIndexPathInfos;
	/**
	 * Index paths that have already been interpolated for the recursion part.
	 */
	private Map<Term, WeakPathInfo> mRecIndexPathInfos;
	/**
	 * The term on the side of the main path to which we rewrite the first shared array. Only needed for mixed
	 * weakeq-ext.
	 */
	private Term[] mRecursionSide;
	/**
	 * The auxiliary variable that is used to build the recursive interpolant in mixed weakeq-ext lemmas.
	 */
	private TermVariable mRecursionVar;
	/**
	 * The auxiliary variable that is used to build the subinterpolants in weakeq-ext lemmas.
	 */
	private TermVariable mDoubleDot;

	@SuppressWarnings("unchecked")
	public ArrayInterpolator(final Interpolator ipolator) {
		mInterpolator = ipolator;
		mTheory = ipolator.mTheory;
		mNumInterpolants = ipolator.mNumInterpolants;
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
		Term maindiseq = mLemmaInfo.getDiseq();
		assert maindiseq instanceof AnnotatedTerm;
		mDiseq = (AnnotatedTerm) maindiseq;
		mDiseqInfo = mInterpolator.getLiteralInfo(maindiseq);
		mEqualities = new HashMap<SymmetricPair<Term>, AnnotatedTerm>();
		mDisequalities = new HashMap<SymmetricPair<Term>, AnnotatedTerm>();
		mABSwitchOccur = mInterpolator.new Occurrence();
		for (final Term literal : mLemmaInfo.getLiterals()) {
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(literal);
			if (litTermInfo.isNegated()) {
				final Term eq = litTermInfo.getAtom();
				assert eq instanceof AnnotatedTerm;
				final ApplicationTerm eqApp = litTermInfo.getEquality();
				mEqualities.put(new SymmetricPair<Term>(eqApp.getParameters()[0], eqApp.getParameters()[1]),
						(AnnotatedTerm) eq);
			} else {
				final ApplicationTerm diseq = litTermInfo.getEquality();
				mDisequalities.put(new SymmetricPair<Term>(diseq.getParameters()[0], diseq.getParameters()[1]),
						(AnnotatedTerm) literal);
			}
		}

		Term[] interpolants = new Term[mNumInterpolants];
		if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
			interpolants = computeReadOverWeakeqInterpolants(proofTerm);
		} else {
			assert mLemmaInfo.getLemmaType().equals(":weakeq-ext");
			interpolants = computeWeakeqExtInterpolants(proofTerm);
		}

		final FormulaUnLet unletter = new FormulaUnLet();
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
	 *            The lemma which interpolants are computed for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeReadOverWeakeqInterpolants(final Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length <= 2;
		if (paths.length == 2) {
			final Term[] indexPath;
			if (paths[0].getIndex() == null) { // TODO Do we need this? This should be the usual order.
				indexPath = paths[0].getPath();
				mStorePath = paths[1];
			} else {
				indexPath = paths[1].getPath();
				mStorePath = paths[0];
			}
			assert indexPath.length == 2;
			mIndexEquality = mEqualities.get(new SymmetricPair<Term>(indexPath[0], indexPath[1]));
		} else { // In this case, the main disequality is of form "a[i] != b[i]"
			mStorePath = paths[0];
		}

		final WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);

		determineInterpolationColor();

		// Determine the shared select index for all partitions where it exists
		arrayPath.mSharedIndex = computeSharedSelectIndices();
		// Compute the interpolant terms from the store path
		mInterpolants = arrayPath.interpolateWeakPathInfo(true);
		// In some cases, the index equality has to be added
		if (mIndexEquality != null) {
			addIndexEqualityReadOverWeakeq(arrayPath);
		}
		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mABSwitchOccur.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
				assert mDiseqInfo.isALocal(color);
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
	 *            The lemma which interpolants are computed for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeWeakeqExtInterpolants(final Term proofTerm) {
		// TODO Find shared arrays for the mixed case. If there are shared arrays for mDiseq, we don't need to build the
		// recursive interpolant but interpolate in such way that all paths in either A or B are closed by shared terms.
		final ProofPath[] paths = mLemmaInfo.getPaths();
		mStorePath = paths[0];
		mIndexPaths = new HashMap<Term, ProofPath>();
		mIndexPathInfos = new HashMap<Term, WeakPathInfo>();
		for (int i = 1; i < paths.length; i++) {
			if (paths[i].getIndex() != null) {
				mIndexPaths.put(paths[i].getIndex(), paths[i]);
			}
		}
		mDoubleDot = mTheory.createFreshTermVariable("ddot", mIndexPaths.keySet().iterator().next().getSort());
		if (mDiseqInfo.getMixedVar() != null) {
			mRecursionSide = new Term[mNumInterpolants];
			mRecursionVar = mTheory.createFreshTermVariable("recursive", mStorePath.getPath()[0].getSort());
			mRecIndexPathInfos = new HashMap<Term, WeakPathInfo>();
		} else {
			// If there are no mixed partitions, we can already determine the way we interpolate. Else, we first have to
			// count for which side we need less recursion steps.
			determineInterpolationColor();
		}

		// Compute the interpolant terms starting on the store path.
		final WeakPathInfo mainPath = new WeakPathInfo(mStorePath);
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
				assert mInterpolants[color].size() == 1;
				interpolants[color] = mInterpolants[color].iterator().next();
			}
		}
		return interpolants;
	}

	/**
	 * Determine how the lemma is interpolated. We say that it is 'B-interpolated' if we summarize A-paths. This
	 * counterintuitive notation results from the fact that we do this when mDiseq is in B. For weakeq-ext, this should
	 * be called after setting mRecursionSide.
	 */
	private void determineInterpolationColor() {
		int color = mNumInterpolants;
		if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq") || mDiseqInfo.getMixedVar() == null) {
			// Compute the first partition where mDiseq is A-local.
			while (true) {
				final int child = getChild(color, mDiseqInfo);
				if (child < 0) {
					break;
				}
				assert mDiseqInfo.isALocal(child);
				color = child;
			}
		} else {
			// Find the first mixed partition where the outer A-path is strictly longer (#stores) than the B-path.
			color = 0;
			while (!mDiseqInfo.isALocal(color)) {
				if (mDiseqInfo.isMixed(color)) {
					final Occurrence recursionInfo = mInterpolator.getOccurrence(mRecursionSide[color]);
					if (recursionInfo.isALocal(color)) {
						color++;
					} else {
						// We found the partition where we switch to A-interpolation (i.e. summarize B-paths)
						break;
					}
				} else {
					color++;
				}
			}
		}
		// All partitions above the computed color (inclusively) have to be interpolated as if mDiseq was A-local
		mABSwitchOccur.occursIn(color);
	}

	/* Read-over-weakeq specific methods */

	/**
	 * Determine for all partitions whether there exists a shared select index. This can be the weakpathindex, if no
	 * index equality exists; the mixed variable if the index equality is mixed; the weakpathindex if the index equality
	 * is local or shared; the other select index if the index equality is A- or B-local and weakpathindex is not
	 * shared. Note: if both select indices are shared, we take weakpathindex. This information is used during
	 * interpolation to determine the partitions where a simple interpolant can be built.
	 */
	private Term[] computeSharedSelectIndices() {
		final Term[] sharedIndices = new Term[mNumInterpolants];
		if (mIndexEquality == null) { // This is the case if the main disequality is of form "a[i] != b[i]"
			// Check if the weakpath index is shared
			final Term index = mStorePath.getIndex();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mInterpolator.getOccurrence(index).isAB(color)) {
					sharedIndices[color] = index;
				}
			}
		} else {
			for (int color = 0; color < mNumInterpolants; color++) {
				// Check if the weakpath index is shared
				if (mInterpolator.getOccurrence(mStorePath.getIndex()).isAB(color)) {
					sharedIndices[color] = mStorePath.getIndex();
				} else {
					final LitInfo info = mInterpolator.getLiteralInfo(mIndexEquality);
					// Check if there is a mixed variable
					if (info.isMixed(color)) {
						sharedIndices[color] = info.getMixedVar();
					} else { // Check the other select index
						final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(mIndexEquality);
						assert info.isALocal(color) || info.isBLocal(color);
						Term otherIndex = termInfo.getEquality().getParameters()[0];
						otherIndex = otherIndex == mStorePath.getIndex() ? termInfo.getEquality().getParameters()[1]
								: otherIndex;
						if (mInterpolator.getOccurrence(otherIndex).isAB(color)) {
							sharedIndices[color] = otherIndex;
						}
					}
				}
			}
		}
		return sharedIndices;
	}

	/**
	 * For a given term, if the term itself is not shared, find an equality literal containing this term and a shared
	 * term on the other side, or a mixed equality.
	 *
	 * @param term
	 *            the term for which we want to find shared terms for all partitions (it can be shared itself)
	 * @return some shared term which equals the given term, or null if there is none
	 */
	private Term[] findSharedTerms(final Term term) {
		Term[] sharedTerms = new Term[mNumInterpolants];
		final Occurrence termOccur = mInterpolator.getOccurrence(term);
		// First check for all partitions if the term itself is shared
		int sharedTermCounter = 0;
		for (int color = 0; color < mNumInterpolants; color++) {
			if (termOccur.isAB(color)) {
				sharedTerms[color] = term;
				sharedTermCounter++;
			}
		}
		if (sharedTermCounter == mNumInterpolants) {
			return sharedTerms;
		}
		// If the term is not shared itself in all partitions, we go through the equalities
		for (final SymmetricPair<Term> eq : mEqualities.keySet()) {
			// Always check first if we still need to search.
			if (sharedTermCounter == mNumInterpolants) {
				return sharedTerms;
			}
			if (eq.getFirst().equals(term) || eq.getSecond().equals(term)) {
				final LitInfo eqInfo = mInterpolator.getLiteralInfo(mEqualities.get(eq));
				for (int color = 0; color < mNumInterpolants; color++) {
					if (eqInfo.isMixed(color)) { // in those partitions, term is local
						sharedTerms[color] = eqInfo.getMixedVar();
					} else if (sharedTerms[color] == null) { // term itself wasn't shared
						final Term otherTerm = eq.getFirst().equals(term) ? eq.getSecond() : eq.getFirst();
						final Occurrence otherOccur = mInterpolator.getOccurrence(otherTerm);
						if (otherOccur.isAB(color)) {
							sharedTerms[color] = otherTerm;
						}
					}
				}
			}
		}
		return sharedTerms;
	}

	/**
	 * For read-over-weakeq, the index equality has to be included in the interpolant if both indices are shared and
	 * either a) it is A-local and the main diseq is mixed or B -> it is added as conjunct to the interpolant, or b) it
	 * is B-local and the main diseq is A -> it is a premise for the path summaries
	 */
	private void addIndexEqualityReadOverWeakeq(WeakPathInfo mainPath) {
		final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
		final InterpolatorLiteralTermInfo diseqInfo = mInterpolator.getLiteralTermInfo(mDiseq);
		final ApplicationTerm mainDiseqApp = diseqInfo.getEquality();
		final Term otherIndex = getIndexFromSelect(mainDiseqApp.getParameters()[0]).equals(mStorePath.getIndex())
				? getIndexFromSelect(mainDiseqApp.getParameters()[1])
				: getIndexFromSelect(mainDiseqApp.getParameters()[0]);
		final Occurrence otherIndexOccur = mInterpolator.getOccurrence(otherIndex);
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mainPath.mSharedIndex[color] != null && mainPath.mSharedIndex[color] == mStorePath.getIndex()) {
				if (mDiseqInfo.isALocal(color) && indexEqInfo.isBLocal(color)) {
					mInterpolants[color].add(mTheory.not(mInterpolator.unquote(mIndexEquality)));
				} else if (!mDiseqInfo.isALocal(color) && indexEqInfo.isALocal(color)) {
					if (otherIndexOccur.isAB(color)) {
						mInterpolants[color].add(mInterpolator.unquote(mIndexEquality));
					}
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

	/* Methods to build the interpolant terms. */

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
		if (left instanceof AnnotatedTerm && (mEqualities.containsValue(left) || left.equals(mDiseq))) {
			final LitInfo selectEq = mInterpolator.getLiteralInfo(left);
			leftSelect = selectEq.getMixedVar();
		} else {
			leftSelect = mTheory.term("select", left, index);
		}
		final Term rightSelect;
		if (right instanceof AnnotatedTerm && (mEqualities.containsValue(right) || right.equals(mDiseq))) {
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
	 * @return a term weq(left,right,order,formula)
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
	 * @return a term nweq(left,right,order,formula)
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
		 * The index i for weak equivalence or weak congruence modulo i. On the main path of weakeq-ext it is null.
		 */
		Term mPathIndex;
		/**
		 * For each partition the shared term for the path index.
		 */
		Term[] mSharedIndex;
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

		/* Specific for weakeq-ext */
		/**
		 * The store indices in the order they appear on the main path in weakeq-ext. An index can appear several times.
		 * In mixed weakeq-ext, we might have to build both the "normal" and the "reverse" subinterpolant for recursion.
		 */
		private Vector<Term> mStores;
		/**
		 * The A- and B-paths on the main path in weakeq-ext.
		 */
		private Vector<StorePath>[] mStorePaths;

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
		}

		/**
		 * Compute the interpolants for the complete weakpath and all partitions for read-over-weakeq and the index
		 * paths of weakeq-ext.
		 *
		 * @param close
		 *            false to get the interpolant of the inner paths only (for the recursion in mixed weakeq-ext)
		 */
		public Set<Term>[] interpolateWeakPathInfo(boolean close) {
			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			// Determine whether to start and end with A or B or AB.
			final Term headTerm, tailTerm;
			if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
				final InterpolatorLiteralTermInfo diseqInfo = mInterpolator.getLiteralTermInfo(mDiseq);
				final Term[] diseqTerms = diseqInfo.getEquality().getParameters();
				if (getArrayFromSelect(diseqTerms[0]).equals(mPath[0])) {
					headTerm = diseqTerms[0];
					tailTerm = diseqTerms[1];
				} else {
					headTerm = diseqTerms[1];
					tailTerm = diseqTerms[0];
				}
			} else {
				headTerm = mPath[0];
				tailTerm = mPath[mPath.length - 1];
			}
			final Occurrence headOccur = mInterpolator.getOccurrence(headTerm);
			final Occurrence tailOccur = mInterpolator.getOccurrence(tailTerm);

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final AnnotatedTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm = left;

				// Each step in a weak path can be either an equality literal or a store step of form "a (store a k v)",
				// or, in weakeq-ext lemmas only, a select equality.
				// In the second and third case, there is no equality literal for the arrays in the lemma.
				if (lit == null) {
					if (mLemmaInfo.getLemmaType().equals(":weakeq-ext")) {
						// Check if the step is a select equality
						final AnnotatedTerm selectEq = findSelectEquality(left, right);
						if (selectEq != null) {
							final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(selectEq);
							final LitInfo stepInfo = mInterpolator.getLiteralInfo(selectEq);
							final ApplicationTerm selectEqApp = termInfo.getEquality();
							Term leftSelect, rightSelect;
							if (getArrayFromSelect(selectEqApp.getParameters()[0]) == left) {
								leftSelect = selectEqApp.getParameters()[0];
								rightSelect = selectEqApp.getParameters()[1];
							} else {
								leftSelect = selectEqApp.getParameters()[1];
								rightSelect = selectEqApp.getParameters()[0];
							}
							// Add the index equality for the first select term
							mTail.closeAPath(mHead, boundaryTerm, stepInfo);
							mTail.openAPath(mHead, boundaryTerm, stepInfo);
							mTail.addSelectIndexEquality(mHead, leftSelect);
							// If the equality is mixed in some partition, we open or close the path at the mixed
							// variable, storing the mixed equality as boundary term.
							if (stepInfo.getMixedVar() != null) {
								final Occurrence rightOcc = mInterpolator.getOccurrence(rightSelect);
								boundaryTerm = selectEq;
								mTail.closeAPath(mHead, boundaryTerm, rightOcc);
								mTail.openAPath(mHead, boundaryTerm, rightOcc);
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
					final Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm);
					final Term storeIndex = getIndexFromStore(storeTerm);
					final AnnotatedTerm indexDiseq =
							mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
					if (indexDiseq != null) {
						final Occurrence indexDiseqOcc = mInterpolator.getLiteralInfo(indexDiseq);
						final Occurrence intersectOcc = stepOcc.intersect(indexDiseqOcc);

						mTail.closeAPath(mHead, boundaryTerm, stepOcc);
						mTail.closeAPath(mHead, boundaryTerm, intersectOcc);
						mTail.openAPath(mHead, boundaryTerm, intersectOcc);
						mTail.openAPath(mHead, boundaryTerm, stepOcc);
						mTail.addIndexDisequality(mHead, storeTerm);
					} else {
						// Otherwise indexDiseq is a trivial disequality like x = x + 1.
						// Treat it as a shared disequality.
						mTail.closeAPath(mHead, boundaryTerm, stepOcc);
						mTail.openAPath(mHead, boundaryTerm, stepOcc);
					}
				} else { // In equality steps, we just close or open A paths.
					final LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (stepInfo.getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right);
						boundaryTerm = stepInfo.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}

			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			// Outer paths have to be closed with mDiseq
			if (close) { // ... unless we want the interpolant for recursion in mixed weakeq-ext
				addDiseq(headOccur, tailOccur);
				closeWeakPath();
			} else {
				closeWeakPath();
			}
			return mPathInterpolants;
		}

		/**
		 * Interpolate the main path of weakeq-ext for all partitions. This also computes the interpolant terms for the
		 * index paths.
		 */
		@SuppressWarnings("unchecked")
		public Set<Term>[] interpolateStorePathInfoExt() {
			// First collect information from the store path: A- and B-paths with their ends and the store indices.
			mStores = new Vector<Term>();
			mStorePaths = new Vector[mNumInterpolants];
			for (int color = 0; color < mNumInterpolants; color++) {
				mStorePaths[color] = new Vector<StorePath>();
			}
			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();
			// Determine whether to start (and end) with A or B or AB and open A paths accordingly.
			final Term headArray = mPath[0];
			final Term tailArray = mPath[mPath.length - 1];
			final Occurrence headOccur = mInterpolator.getOccurrence(headArray);
			final Occurrence tailOccur = mInterpolator.getOccurrence(tailArray);

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);
			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final AnnotatedTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm;
				boundaryTerm = left;

				// Each step in the main path is either an equality literal or a store step of form "a (store a i v)".
				// In the second case, there is no literal in the lemma.
				if (lit == null) {
					// A store step can only open or close a path at term "a" if "a" is the left term.
					final Term storeTerm, arrayTerm;
					if (isStoreTerm(left) && getArrayFromStore(left).equals(right)) {
						storeTerm = left;
						arrayTerm = right;
					} else {
						storeTerm = right;
						arrayTerm = left;
					}
					assert getArrayFromStore(storeTerm).equals(arrayTerm);
					final Term storeIndex = getIndexFromStore(storeTerm);
					final Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm);
					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addStoreIndex(mHead, storeIndex);
					mStores.add(storeIndex);
				} else { // In equality steps, we just close or open A paths.
					final LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (stepInfo.getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right);
						boundaryTerm = stepInfo.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}
			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			addDiseq(headOccur, tailOccur);
			closeWeakeqExt(headOccur, tailOccur);
			// Now we have collected all information to build the "outer interpolant terms" for the store path.

			// For the mixed case, we want to keep the recursion steps small
			if (mDiseqInfo.getMixedVar() != null) {
				for (int color = 0; color < mNumInterpolants; color++) {
					if (mDiseqInfo.isMixed(color)) {
						final StorePath left = mStorePaths[color].get(0);
						final StorePath right = mStorePaths[color].get(mStorePaths[color].size() - 1);
						final int leftSteps = left.mStores != null ? left.mStores.size() : 0;
						final int rightSteps = right.mStores != null ? right.mStores.size() : 0;

						if (leftSteps <= rightSteps) {
							mRecursionSide[color] = mPath[0];
						} else {
							mRecursionSide[color] = mPath[mPath.length - 1];
						}
					}
				}
				determineInterpolationColor();
			}

			// Now we build all subinterpolants
			for (int i = 0; i < mStores.size(); i++) {
				final Term index = mStores.get(i);
				final Occurrence indexInfo = mInterpolator.getOccurrence(index);
				if (!mIndexPathInfos.containsKey(index)) {
					WeakPathInfo indexPath = new WeakPathInfo(mIndexPaths.get(index));
					final Term[] sharedIndex = findSharedTerms(index);
					indexPath.mSharedIndex = sharedIndex;
					for (int color = 0; color < mNumInterpolants; color++) {
						if (sharedIndex[color] == null) {
							if (indexInfo.isALocal(color) && mABSwitchOccur.isBLocal(color)
									|| indexInfo.isBLocal(color) && mABSwitchOccur.isALocal(color)) {
								// In this case, the index path interpolant will be included in an (n)weq term
								indexPath.mSharedIndex[color] = mDoubleDot;
							}
						}
					}
					indexPath.interpolateWeakPathInfo(true);
					mIndexPathInfos.put(index, indexPath);
				}
			}

			// Then build the interpolant terms for the store path.
			for (int color = 0; color < mNumInterpolants; color++) {
				StorePath recursionPath = null;
				for (final StorePath storePath : mStorePaths[color]) {
					// Add all interpolant terms except for the outer paths in weakeq-ext.
					if (mDiseqInfo.isMixed(color) && mRecursionSide[color] == mPath[0] && storePath.mLeft == null
							|| mDiseqInfo.isMixed(color) && mRecursionSide[color] == mPath[mPath.length - 1]
									&& storePath.mRight == null) {
						recursionPath = storePath;
					} else {
						mTail.addInterpolantClauseExt(color, storePath);
					}
				}
				if (mDiseqInfo.isMixed(color)) {
					final WeakPathEnd recSide = mRecursionSide[color] == mPath[0] ? mHead : mTail;
					final WeakPathEnd other = recSide == mHead ? mTail : mHead;
					recSide.buildRecursiveInterpolant(color, other, recursionPath);
				}
			}

			return mPathInterpolants;
		}

		/**
		 * For a step in an index path of an extensionality lemma that is not an array equality, check if we can find a
		 * select equality between the arrays and corresponding index equalities.
		 *
		 * @return the select equality if it exists, else null.
		 */
		private AnnotatedTerm findSelectEquality(final Term leftArray, final Term rightArray) {
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
			// No select equality could be found.
			return null;
		}

		/**
		 * Close the path using the main disequality.
		 *
		 * @param headOcc
		 *            The occurrence of the term in the diseq corresponding to the left path end
		 * @param tailOcc
		 *            The occurrence of the term in the diseq corresponding to the right path end
		 */
		public void addDiseq(Occurrence headOcc, Occurrence tailOcc) {
			Term boundaryTailTerm, boundaryHeadTerm;
			boundaryHeadTerm = mPath[0];
			boundaryTailTerm = mPath[mPath.length - 1];
			if (mDiseqInfo.getMixedVar() == null) {
				// In each case, if this closes or opens A-paths, boundary_Term is shared.
				mHead.closeAPath(mTail, boundaryHeadTerm, mABSwitchOccur);
				mHead.openAPath(mTail, boundaryHeadTerm, mABSwitchOccur);
				mTail.closeAPath(mHead, boundaryTailTerm, mABSwitchOccur);
				mTail.openAPath(mHead, boundaryTailTerm, mABSwitchOccur);
			} else {
				mHead.closeAPath(mTail, boundaryHeadTerm, headOcc);
				mHead.openAPath(mTail, boundaryHeadTerm, headOcc);
				mHead.closeAPath(mTail, boundaryHeadTerm, mDiseqInfo);
				mTail.closeAPath(mHead, boundaryTailTerm, tailOcc);
				mTail.openAPath(mHead, boundaryTailTerm, tailOcc);
				mTail.closeAPath(mHead, boundaryTailTerm, mDiseqInfo);

				if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
					if (mIndexEquality != null) {
						final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
						mTail.addSelectIndexEqAllColors(mHead, indexEqInfo, mIndexEquality, indexEqInfo);
					}

					mHead.closeAPath(mTail, mDiseq, tailOcc);
					mTail.closeAPath(mHead, mDiseq, headOcc);
				} else {
					if (mPathIndex != null) { // On the store path, we need to handle the mixed case separately
						mHead.closeAPath(mTail, mRecursionVar, mABSwitchOccur);
						mHead.openAPath(mTail, mRecursionVar, mABSwitchOccur);
						mTail.closeAPath(mHead, mRecursionVar, mABSwitchOccur);
						mTail.openAPath(mHead, mRecursionVar, mABSwitchOccur);
					}
				}
			}
		}

		/**
		 * Close the outer paths which are still open at the left or right end. This adds FPiA/FPiB terms.
		 */
		private void closeWeakPath() {
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mABSwitchOccur.isALocal(color)) {
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					// A-local outer paths must be closed here, B-local ones are already closed.
					if (mHead.mTerm[color] != null) {
						mHead.addInterpolantClauseAPath(color, null);
					}
					if (mTail.mTerm[color] != null) {
						mTail.addInterpolantClauseAPath(color, null);
					}
					// The whole path and the diseq are in A, but there can still be B index(dis)eqs
					if (mHead.mLastChange[color] == null && mTail.mLastChange[color] == null) {
						// In this case, they are stored in mHead
						mHead.addInterpolantClauseAPath(color, null);
					}
				} else {
					// B-local paths must be closed, A-local ones are already closed.
					if (mHead.mLastChange[color] != mHead.mTerm[color]) {
						mHead.addInterpolantClauseBPath(color, null);
					}
					if (mTail.mLastChange[color] != mTail.mTerm[color]) {
						mTail.addInterpolantClauseBPath(color, null);
					}
					// The whole path and the diseq are in B, but there can still be A index(dis)eqs
					if (mHead.mLastChange[color] == null && mTail.mLastChange[color] == null) {
						// In this case, they are stored in mHead
						mHead.addInterpolantClauseBPath(color, null);
					}
				}
			}
		}

		/**
		 * Close the store path of an extensionality lemma.
		 *
		 * @param headOcc
		 *            the occurrence of the left store path end
		 * @param tailOcc
		 *            the occurrence of the right store path end
		 */
		private void closeWeakeqExt(final Occurrence headOcc, final Occurrence tailOcc) {
			while (mHead.mColor < mMaxColor || mTail.mColor < mMaxColor) {
				if (mHead.mColor < mTail.mColor) { // the left outer path is an A-path
					if (mDiseqInfo.isMixed(mHead.mColor)) {
						mHead.mColor = getParent(mHead.mColor);
					} else {
						mHead.closeSingleAPath(mTail, mPath[0]);
					}
				} else if (mHead.mColor == mTail.mColor) { // both outer paths are A
					if (!mDiseqInfo.isALocal(mHead.mColor)) {
						assert mDiseqInfo.isAB(mHead.mColor);
						mHead.closeSingleAPath(mTail, mPath[0]);
						mTail.closeSingleAPath(mHead, mPath[mPath.length - 1]);
					} else {
						mHead.mColor = mTail.mColor = getParent(mHead.mColor);
					}
				} else { // the right outer path is an A-path
					if (mDiseqInfo.isMixed(mTail.mColor)) {
						mTail.mColor = getParent(mTail.mColor);
					} else {
						mTail.closeSingleAPath(mHead, mPath[mPath.length - 1]);
					}
				}
			}
			// Then, close the other outer paths. TODO Can we simplify this?
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mDiseqInfo.isALocal(color)) {
					// A-local outer paths must be closed here, B-local ones are already closed.
					if (mHead.mTerm[color] != mPath[0]) {
						mHead.addStorePathAExt(color, null);
					}
					if (mTail.mTerm[color] != mPath[mPath.length - 1]) {
						mTail.addStorePathAExt(color, null);
					}
				} else if (mDiseqInfo.isBorShared(color)) {
					// B-local outer paths must be closed, A-local ones are already closed.
					if (mHead.mLastChange[color] != mPath[0]) {
						mHead.addStorePathBExt(color, null);
					}
					if (mTail.mLastChange[color] != mPath[mPath.length - 1]) {
						mTail.addStorePathBExt(color, null);
					}
				} else {
					if (headOcc.isALocal(color)) {
						if (mHead.mTerm[color] != mPath[0]) {
							mHead.addStorePathAExt(color, null);
						}
						if (mTail.mTerm[color] != mPath[mPath.length - 1]) {
							mTail.addStorePathBExt(color, null);
						}
					} else {
						if (mHead.mLastChange[color] != mPath[0]) {
							mHead.addStorePathBExt(color, null);
						}
						if (mTail.mLastChange[color] != mPath[mPath.length - 1]) {
							mTail.addStorePathAExt(color, null);
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
				final Map<AnnotatedTerm, LitInfo> indexDiseqs, final Map<AnnotatedTerm, LitInfo> indexEqs) {
			if (indexDiseqs == null && indexEqs == null) {
				return mTheory.mFalse;
			}
			final Set<Term> indexTerms = new HashSet<Term>();
			if (indexDiseqs != null) {
				for (final AnnotatedTerm diseq : indexDiseqs.keySet()) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(diseq);
					final LitInfo info = indexDiseqs.get(diseq);
					final ApplicationTerm diseqApp = termInfo.getEquality();
					// Index diseqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the store index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: diseqApp.getParameters()[0].equals(mPathIndex) ? diseqApp.getParameters()[1]
									: diseqApp.getParameters()[0];
					indexTerms.add(mTheory.equals(index, sharedIndex));
				}
			}
			if (indexEqs != null) {
				for (final AnnotatedTerm eq : indexEqs.keySet()) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(eq);
					final LitInfo info = indexEqs.get(eq);
					final ApplicationTerm eqApp = termInfo.getEquality();
					// Index eqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the select index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: eqApp.getParameters()[0].equals(mPathIndex) ? eqApp.getParameters()[1]
									: eqApp.getParameters()[0];
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
				final Map<AnnotatedTerm, LitInfo> indexDiseqs, final Map<AnnotatedTerm, LitInfo> indexEqs) {
			if (indexDiseqs == null && indexEqs == null) {
				return mTheory.mTrue;
			}
			final Set<Term> indexTerms = new HashSet<Term>();
			if (indexDiseqs != null) {
				for (final AnnotatedTerm diseq : indexDiseqs.keySet()) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(diseq);
					final LitInfo info = indexDiseqs.get(diseq);
					final ApplicationTerm diseqApp = termInfo.getEquality();
					// Index diseqs are either mixed or A-local.
					// In the first case, there is a mixed term, in the second, the store index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: diseqApp.getParameters()[0].equals(mPathIndex) ? diseqApp.getParameters()[1]
									: diseqApp.getParameters()[0];
					if (info.isMixed(color)) { // Add the A projection of the index diseq (an eq in the mixed case)
						indexTerms.add(mTheory.equals(index, sharedIndex));
					} else if (info.isALocal(color)) {
						// If the index diseq is A local, the A projection is the diseq itself.
						indexTerms.add(mTheory.not(mTheory.equals(index, sharedIndex)));
					}
				}
			}
			if (indexEqs != null) {
				for (final AnnotatedTerm eq : indexEqs.keySet()) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(eq);
					final LitInfo info = indexEqs.get(eq);
					final ApplicationTerm eqApp = termInfo.getEquality();
					// Index eqs are either mixed or B-local.
					// In the first case, there is a mixed term, in the second, the select index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: eqApp.getParameters()[0].equals(mPathIndex) ? eqApp.getParameters()[1]
									: eqApp.getParameters()[0];
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
			Map<AnnotatedTerm, LitInfo>[] mIndexDiseqs;
			/**
			 * For each partition this contains the set of B(resp. A)-local and mixed select index equalities found on
			 * the A (resp. B) path so far.
			 */
			Map<AnnotatedTerm, LitInfo>[] mIndexEqs;
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
						addStorePathAExt(color, boundary);
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
							addStorePathBExt(child, boundary);
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
				final AnnotatedTerm diseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
				final LitInfo diseqInfo = mInterpolator.getLiteralInfo(diseq);

				// The diseq has to be added to all partitions where it is mixed and all partitions that lie on the
				// tree path between the partition of the diseq and the partition of the store term.
				// In nodes under the lca which are not on the way, both are in B, in nodes above the lca both are in A,
				// and in both cases there is nothing to do.
				addIndexDiseqAllColors(other, diseqInfo, diseq, diseqInfo);
				if (diseqInfo.getMixedVar() != null) {
					// Additionally go up and down with weakpathindexoccur
					final Occurrence occur = mInterpolator.getOccurrence(mPathIndex);
					addIndexDiseqAllColors(other, occur, diseq, diseqInfo);
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index disequality to
			 * those partitions. This adds the index disequality to all partitions where it is not in A (resp. B) while
			 * the path is.
			 */
			private void addIndexDiseqAllColors(final WeakPathEnd other, final Occurrence occur,
					final AnnotatedTerm diseq, final LitInfo diseqInfo) {
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
			private void addIndexDiseqOneColor(final WeakPathEnd other, final AnnotatedTerm diseq,
					final LitInfo diseqInfo, final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexDiseqs[color] == null) {
						other.mIndexDiseqs[color] = new HashMap<AnnotatedTerm, LitInfo>();
					}
					other.mIndexDiseqs[color].put(diseq, diseqInfo);
				} else { // Else in this one.
					if (mIndexDiseqs[color] == null) {
						mIndexDiseqs[color] = new HashMap<AnnotatedTerm, LitInfo>();
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
					final AnnotatedTerm indexEq = mEqualities.get(new SymmetricPair<Term>(selectIndex, mPathIndex));
					final LitInfo eqInfo = mInterpolator.getLiteralInfo(indexEq);
					addSelectIndexEqAllColors(other, eqInfo, indexEq, eqInfo);
					if (eqInfo.getMixedVar() != null) {
						final Occurrence occur = mInterpolator.getOccurrence(mPathIndex);
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
					final AnnotatedTerm eq, final LitInfo eqInfo) {
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
			private void addSelectIndexEqOneColor(final WeakPathEnd other, final AnnotatedTerm eq, final LitInfo eqInfo,
					final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexEqs[color] == null) {
						other.mIndexEqs[color] = new HashMap<AnnotatedTerm, LitInfo>();
					}
					other.mIndexEqs[color].put(eq, eqInfo);
				} else { // Else in this one.
					if (mIndexEqs[color] == null) {
						mIndexEqs[color] = new HashMap<AnnotatedTerm, LitInfo>();
					}
					mIndexEqs[color].put(eq, eqInfo);
				}
			}

			/**
			 * Add the store index of a store step in the main path of weakeq-ext.
			 *
			 * @param other
			 *            the other path end
			 * @param storeTerm
			 *            the store term from which we extract the index
			 */
			private void addStoreIndex(final WeakPathEnd other, final Term storeIndex) {
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
					final Term index = mSharedIndex[color];
					final Term fPiA = buildFPiATerm(color, index, mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
					if (mABSwitchOccur.isALocal(color)) { // Case (ii)
						assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
						if (!(fPiA.equals(mTheory.mFalse))) {
							assert mSharedIndex[color] == mPathIndex || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
						}
						mPathInterpolants[color].add(fPiA);
					} else { // Case (i)
						final Term selectEq = buildSelectEq(left, right, index);
						final Term itpClause = mTheory.or(selectEq, fPiA);
						mPathInterpolants[color].add(itpClause);
					}
				} else if (mABSwitchOccur.isALocal(color)) { // Case (iv)
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
						assert mIndexDiseqs[color] == null;
					} else { // Can happen when the reverse interpolant is built
						// TODO Is there anything to do, or does this only happen, when the recursive interpolant is not
						// needed? Because otherwise, we should have a shared index.
						assert mIndexDiseqs[color] == null || !mDiseqInfo.isMixed(color);
					}
				} else { // Case (iii)
					assert mABSwitchOccur.isBLocal(color);
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
				if (mSharedIndex[color] != null) {
					final Term index = mSharedIndex[color];
					final Term fPiB = buildFPiBTerm(color, index, mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
					if (mABSwitchOccur.isALocal(color)) { // Case (ii)
						assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext"); // TEST
						final Term selectDiseq = mTheory.not(buildSelectEq(left, right, index));
						final Term itpClause = mTheory.and(selectDiseq, fPiB);
						mPathInterpolants[color].add(itpClause);
					} else { // Case (i)
						mPathInterpolants[color].add(fPiB);
					}
				} else if (mABSwitchOccur.isALocal(color)) { // Case (iv)
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					final Term fPiB = buildFPiBTerm(color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;
					final Term itpClause = buildNweqTerm(left, right, order, fPiB, cdot);
					mPathInterpolants[color].add(itpClause);
				} else { // Case (iii)
					assert mABSwitchOccur.isBLocal(color);
					assert mDiseqInfo.isBLocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
						assert mIndexDiseqs[color] == null;
					} else { // Can happen when recursive interpolant is built
						// TODO Is there anything to do, or does this only happen, when the recursive interpolant is not
						// needed? Because otherwise, we should have a shared index.
						assert mIndexDiseqs[color] == null || !mDiseqInfo.isMixed(color);
					}
				}
			}

			/**
			 * Add an A store path to the main path in weakeq-ext. This stores all the information needed to compute the
			 * interpolant terms once we have traversed the whole main path and computed all sub-interpolants.
			 *
			 * @param color
			 *            The current partition
			 * @param boundary
			 *            The term closing this path
			 */
			private void addStorePathAExt(final int color, final Term boundary) {
				addStorePathExt(color, boundary, true);
			}

			/**
			 * Add a B store path to the main path in weakeq-ext. This stores all the information that needed to compute
			 * the interpolant terms once we have traversed the whole main path and computed all sub-interpolants.
			 *
			 * @param color
			 *            The current partition
			 * @param boundary
			 *            The term closing this path
			 */
			private void addStorePathBExt(final int color, final Term boundary) {
				addStorePathExt(color, boundary, false);
			}

			/**
			 * Add an A or B store path to the main path in weakeq-ext. This stores all the information that needed to
			 * compute the interpolant terms once we have traversed the whole main path and computed all
			 * sub-interpolants.
			 *
			 * @param color
			 * @param boundary
			 * @param isAPath
			 */
			private void addStorePathExt(final int color, final Term boundary, final boolean isAPath) {
				final Term left, right;
				if (this.equals(mTail)) {
					left = mLastChange[color];
					right = boundary;
				} else { // This is needed when we close the left outer paths.
					left = boundary;
					right = mLastChange[color];
				}
				final Set<Term> stores = mStoreIndices[color];
				final StorePath storePath = new StorePath(left, right, stores, isAPath);
				if (this.equals(mTail)) {
					mStorePaths[color].add(storePath);
				} else { // This is the left outer path
					mStorePaths[color].add(0, storePath);
				}
				if (left != null && right != null) {
					// We want to keep the store indices on the outer paths, so we can use them for the recursive
					// interpolant. This happens only in closeWeakeqExt
					mStoreIndices[color] = null;
				}
			}

			/**
			 * Add the interpolant clause for a store path in weakeq-ext.
			 *
			 * @param color
			 *            The current partition.
			 * @param storePath
			 *            The A or B store path on the main path.
			 */
			void addInterpolantClauseExt(final int color, final StorePath storePath) {
				if (storePath.mIsAPath) {
					addInterpolantClauseAPathExt(color, storePath);
				} else {
					addInterpolantClauseBPathExt(color, storePath);
				}
			}

			/**
			 * Compute the interpolant term for an A store path on the main path in weakeq-ext. This is called only
			 * after all subinterpolants have been computed.
			 *
			 * @param color
			 *            The current partition
			 * @param storePath
			 *            The A-colored store path.
			 */
			void addInterpolantClauseAPathExt(final int color, final StorePath storePath) {
				if (mABSwitchOccur.isBLocal(color)) {
					final Term left = storePath.mLeft;
					final Term right = storePath.mRight;
					assert left != null && right != null;
					if (storePath.mStores != null) {
						final Set<Term> subInterpolants = new HashSet<Term>();
						Set<Term> sharedIndices = new HashSet<Term>();
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant = mTheory.and(
									indexPath.mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
							if (indexPath.mSharedIndex[color] != null && indexPath.mSharedIndex[color] != mDoubleDot) {
								sharedIndices.add(indexPath.mSharedIndex[color]);
								mPathInterpolants[color].add(subInterpolant);
							} else {
								subInterpolants.add(subInterpolant);
							}
						}
						// With shared indices, we can shorten the weq-term by rewriting left to right at those indices
						final int order =
								storePath.mStores == null ? 0 : storePath.mStores.size() - sharedIndices.size();
						Term rewriteLeftAtShared = left;
						for (final Term idx : sharedIndices) {
							rewriteLeftAtShared =
									mTheory.term("store", rewriteLeftAtShared, idx, mTheory.term("select", right, idx));
						}
						final Term formula = mTheory.or(subInterpolants.toArray(new Term[subInterpolants.size()]));
						// The interpolant is a weq term including the sub-interpolants of local index terms
						final Term weqTerm = buildWeqTerm(rewriteLeftAtShared, right, order, formula, mDoubleDot);
						mPathInterpolants[color].add(weqTerm);
					} else {
						mPathInterpolants[color].add(mTheory.equals(left, right));
					}
				} else {
					assert mDiseqInfo.isALocal(color) || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
					if (storePath.mStores != null) {
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant = mTheory.or(
									indexPath.mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
							mPathInterpolants[color].add(subInterpolant);
						}
					}
				}
			}

			/**
			 * Compute the interpolant term for a B store path on the main path in weakeq-ext. This is called only after
			 * all subinterpolants have been computed.
			 *
			 * @param color
			 *            The current partition
			 * @param storePath
			 *            The B-colored store path.
			 */
			void addInterpolantClauseBPathExt(final int color, final StorePath storePath) {
				if (mABSwitchOccur.isALocal(color)) {
					assert mDiseqInfo.isALocal(color) || mDiseqInfo.isMixed(color);
					final Term left = storePath.mLeft;
					final Term right = storePath.mRight;
					assert left != null && right != null;
					if (storePath.mStores != null) {
						final Set<Term> subInterpolants = new HashSet<Term>();
						Set<Term> sharedIndices = new HashSet<Term>();
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant = mTheory.or(
									indexPath.mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
							if (indexPath.mSharedIndex[color] != null && indexPath.mSharedIndex[color] != mDoubleDot) {
								sharedIndices.add(indexPath.mSharedIndex[color]);
								mPathInterpolants[color].add(subInterpolant);
							} else {
								subInterpolants.add(subInterpolant);
							}
						}
						// With shared indices, we can shorten the nweq-term by rewriting left to right at those indices
						final int order =
								storePath.mStores == null ? 0 : storePath.mStores.size() - sharedIndices.size();
						Term rewriteLeftAtShared = left;
						for (final Term idx : sharedIndices) {
							rewriteLeftAtShared =
									mTheory.term("store", rewriteLeftAtShared, idx, mTheory.term("select", right, idx));
						}
						final Term formula = mTheory.and(subInterpolants.toArray(new Term[subInterpolants.size()]));
						// The interpolant is an nweq term including the sub-interpolants of local index terms
						final Term weqTerm = buildNweqTerm(rewriteLeftAtShared, right, order, formula, mDoubleDot);
						mPathInterpolants[color].add(weqTerm);
					} else {
						mPathInterpolants[color].add(mTheory.not(mTheory.equals(left, right)));
					}
				} else {
					assert mDiseqInfo.isBorShared(color) || mDiseqInfo.isMixed(color);
					if (storePath.mStores != null) {
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant = mTheory.and(
									indexPath.mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
							mPathInterpolants[color].add(subInterpolant);
						}
					}
				}
			}

			/**
			 * Build the recursive interpolant for mixed weakeq-ext.
			 *
			 * @param color
			 *            The current partition
			 * @param other
			 *            The other path end
			 * @param recursionPath
			 *            The path on which we rewrite the shared array to the outer path end.
			 */
			void buildRecursiveInterpolant(final int color, WeakPathEnd other, final StorePath recursionPath) {
				if (recursionPath.mIsAPath) {
					buildRecursiveInterpolantAPath(color, other, recursionPath);
				} else {
					buildRecursiveInterpolantBPath(color, other, recursionPath);
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
			void buildRecursiveInterpolantAPath(final int color, final WeakPathEnd other,
					final StorePath recursionPath) {
				// Build the innermost interpolant term "mixedVar=recursionVar /\ B-Interpolant"
				final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), mRecursionVar);
				final Term bInterpolant =
						mTheory.and(mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				mPathInterpolants[color].clear();
				Term recursiveInterpolant = mTheory.and(eqTerm, bInterpolant);
				TermVariable lastRecVar = mRecursionVar;

				// Recursion over the store indices on this outer path
				if (recursionPath.mStores != null) {
					for (final Term index : recursionPath.mStores) {
						final TermVariable currentRecVar =
								mTheory.createFreshTermVariable("recursive", mRecursionVar.getSort());
						final Term rewriteAtIndex, rewriteToArray, rewriteWithElement;
						final WeakPathInfo indexPath;
						final Set<Term> recPathInterpolantTerms;
						final Term pathInterpolant;
						if (mRecIndexPathInfos.containsKey(index)) {
							indexPath = mRecIndexPathInfos.get(index);
							recPathInterpolantTerms = indexPath.mPathInterpolants[color];
						} else {
							indexPath = new WeakPathInfo(mIndexPaths.get(index));
							indexPath.mSharedIndex = findSharedTerms(index);
							// Compute the reverse itp
							BitSet oldInA = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = oldInA;
							indexPath.interpolateWeakPathInfo(false); // Compute the reverse itp for the inner path only
							// Change back
							oldInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = oldInA;
							recPathInterpolantTerms = indexPath.mPathInterpolants[color];
						}

						if (indexPath.mSharedIndex[color] != null) { // Case 5.3 (i)
							rewriteAtIndex = indexPath.mSharedIndex[color];
							pathInterpolant = mTheory
									.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							final Term lastSharedOnIndexPath = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
									: indexPath.mHead.mLastChange[color];
							if (lastSharedOnIndexPath instanceof AnnotatedTerm
									&& mEqualities.containsValue(lastSharedOnIndexPath)) {
								rewriteToArray = null;
								// Last change was at a mixed select equality
								final LitInfo selectEq = mInterpolator.getLiteralInfo(lastSharedOnIndexPath);
								rewriteWithElement = selectEq.getMixedVar();
							} else {
								rewriteToArray = lastSharedOnIndexPath;
								rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
							}
						} else { // Case 5.3 (ii)
							final TermVariable cdot = mTheory.createFreshTermVariable("cdot", index.getSort());
							rewriteAtIndex = cdot;
							pathInterpolant = mTheory
									.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							final Term lastSharedOnIndexPath = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
									: indexPath.mHead.mLastChange[color];
							assert !(lastSharedOnIndexPath instanceof AnnotatedTerm
									&& mEqualities.containsValue(lastSharedOnIndexPath));
							rewriteToArray = lastSharedOnIndexPath;
							rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
						}
						// Build the FPiBTerm for the outer B path of the index path
						final Term fPiB;
						// Needed for case without shared index (then there are no indexEqs)
						final int fPiBOrderForRecursion;
						if (this.equals(mHead)) { // The right outer path is the B path
							final Map<AnnotatedTerm, LitInfo> indexDiseqs = indexPath.mTail.mIndexDiseqs[color];
							fPiBOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPiB = indexPath.buildFPiBTerm(color, rewriteAtIndex, indexDiseqs,
									indexPath.mTail.mIndexEqs[color]);
						} else { // The left outer path is the B path
							final Map<AnnotatedTerm, LitInfo> indexDiseqs = indexPath.mHead.mIndexDiseqs[color];
							fPiBOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPiB = indexPath.buildFPiBTerm(color, rewriteAtIndex, indexDiseqs,
									indexPath.mHead.mIndexEqs[color]);
						}
						// Insert the rewritten term into the inner interpolant term
						final Term rewriteRecVar =
								mTheory.term("store", currentRecVar, rewriteAtIndex, rewriteWithElement);
						final Term rewriteRecInterpolant =
								mTheory.and(fPiB, mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant));
						// Build the final recursive interpolant
						if (indexPath.mSharedIndex[color] != null) {
							recursiveInterpolant = mTheory.or(pathInterpolant, rewriteRecInterpolant);
						} else {
							assert rewriteAtIndex instanceof TermVariable;
							assert rewriteToArray != null;
							final TermVariable nweqDot = (TermVariable) rewriteAtIndex;
							final Set<Term> nweqTerms = new HashSet<Term>();
							// Build the nweq terms for all inner paths
							for (final StorePath path : mStorePaths[color]) {
								final Term left = path.mLeft;
								final Term right = path.mRight;
								if (left != null && right != null) {
									final int order = path.mStores != null ? path.mStores.size() : 0;
									final Term nweqTerm =
											buildNweqTerm(left, right, order, rewriteRecInterpolant, nweqDot);
									nweqTerms.add(nweqTerm);
								}
							}
							// Build the nweq term for the concatenation of the outer B-paths on store and index path
							final Term concatLeft = other.mLastChange[color];
							final Term concatRight = rewriteToArray;
							final Set<Term> otherMainStores = other.mStoreIndices[color];
							final int concatStores =
									fPiBOrderForRecursion + (otherMainStores == null ? 0 : otherMainStores.size());
							final Term concatNweqTerm = buildNweqTerm(concatLeft, concatRight, concatStores,
									rewriteRecInterpolant, nweqDot);
							nweqTerms.add(concatNweqTerm);
							final Term nweqPart = mTheory.or(nweqTerms.toArray(new Term[nweqTerms.size()]));
							recursiveInterpolant = mTheory.let(lastRecVar, currentRecVar, recursiveInterpolant);
							recursiveInterpolant = mTheory.or(recursiveInterpolant, pathInterpolant, nweqPart);
						}
						lastRecVar = currentRecVar;
					}
				}
				// Replace the recursionVar by the first shared term
				recursiveInterpolant = mTheory.let(lastRecVar, mLastChange[color], recursiveInterpolant);
				mPathInterpolants[color].add(recursiveInterpolant);
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
			void buildRecursiveInterpolantBPath(final int color, final WeakPathEnd other,
					final StorePath recursionPath) {
				// Build the innermost interpolant term "mixedVar=recursionVar /\ B-Interpolant"
				final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), mRecursionVar);
				final Term aInterpolant =
						mTheory.or(mPathInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
				mPathInterpolants[color].clear();
				Term recursiveInterpolant = mTheory.or(eqTerm, aInterpolant);
				TermVariable lastRecVar = mRecursionVar;

				// Recursion over the store indices on this outer path
				if (recursionPath.mStores != null) {
					for (final Term index : recursionPath.mStores) {
						final TermVariable currentRecVar =
								mTheory.createFreshTermVariable("recursive", mRecursionVar.getSort());
						final Term rewriteAtIndex, rewriteToArray, rewriteWithElement;
						final WeakPathInfo indexPath;
						final Set<Term> recPathInterpolantTerms;
						final Term pathInterpolant;
						if (mRecIndexPathInfos.containsKey(index)) {
							indexPath = mRecIndexPathInfos.get(index);
							recPathInterpolantTerms = indexPath.mPathInterpolants[color];
						} else {
							indexPath = new WeakPathInfo(mIndexPaths.get(index));
							indexPath.mSharedIndex = findSharedTerms(index);
							// Compute the reverse itp
							BitSet oldInA = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = oldInA;
							indexPath.interpolateWeakPathInfo(false); // Compute the reverse itp for the inner path only
							mRecIndexPathInfos.put(index, indexPath);
							// Change back
							oldInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = oldInA;
							recPathInterpolantTerms = indexPath.mPathInterpolants[color];
						}

						if (indexPath.mSharedIndex[color] != null) { // Case 5.3 (i)
							rewriteAtIndex = indexPath.mSharedIndex[color];
							pathInterpolant = mTheory
									.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							final Term lastSharedOnIndexPath = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
									: indexPath.mHead.mLastChange[color];
							if (lastSharedOnIndexPath instanceof AnnotatedTerm
									&& mEqualities.containsValue(lastSharedOnIndexPath)) {
								rewriteToArray = null;
								// Last change was at a mixed select equality
								final LitInfo selectEq = mInterpolator.getLiteralInfo(lastSharedOnIndexPath);
								rewriteWithElement = selectEq.getMixedVar();
							} else {
								rewriteToArray = lastSharedOnIndexPath;
								rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
							}
						} else { // Case 5.3 (ii)
							final TermVariable cdot = mTheory.createFreshTermVariable("cdot", index.getSort());
							rewriteAtIndex = cdot;
							pathInterpolant = mTheory
									.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							final Term lastSharedOnIndexPath = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
									: indexPath.mHead.mLastChange[color];
							assert !(lastSharedOnIndexPath instanceof AnnotatedTerm
									&& mEqualities.containsValue(lastSharedOnIndexPath));
							rewriteToArray = lastSharedOnIndexPath;
							rewriteWithElement = mTheory.term("select", rewriteToArray, rewriteAtIndex);
						}
						// Build the FPiATerm for the outer A path of the index path
						final Term fPiA;
						// Needed for case without shared index (then there are no indexEqs)
						final int fPiAOrderForRecursion;
						if (this.equals(mHead)) { // The right outer path is the B path
							final Map<AnnotatedTerm, LitInfo> indexDiseqs = indexPath.mTail.mIndexDiseqs[color];
							fPiAOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPiA = indexPath.buildFPiATerm(color, rewriteAtIndex, indexDiseqs,
									indexPath.mTail.mIndexEqs[color]);
						} else { // The left outer path is the B path
							final Map<AnnotatedTerm, LitInfo> indexDiseqs = indexPath.mHead.mIndexDiseqs[color];
							fPiAOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPiA = indexPath.buildFPiATerm(color, rewriteAtIndex, indexDiseqs,
									indexPath.mHead.mIndexEqs[color]);
						}
						// Insert the rewritten term into the inner interpolant term
						final Term rewriteRecVar =
								mTheory.term("store", currentRecVar, rewriteAtIndex, rewriteWithElement);
						final Term rewriteRecInterpolant =
								mTheory.or(fPiA, mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant));
						// Build the final recursive interpolant
						if (indexPath.mSharedIndex[color] != null) {
							recursiveInterpolant = mTheory.and(pathInterpolant, rewriteRecInterpolant);
						} else {
							assert rewriteAtIndex instanceof TermVariable;
							assert rewriteToArray != null;
							final TermVariable weqDot = (TermVariable) rewriteAtIndex;
							final Set<Term> weqTerms = new HashSet<Term>();
							// Build the weq terms for all inner paths
							for (final StorePath path : mStorePaths[color]) {
								final Term left = path.mLeft;
								final Term right = path.mRight;
								if (left != null && right != null) {
									final int order = path.mStores != null ? path.mStores.size() : 0;
									final Term weqTerm =
											buildWeqTerm(left, right, order, rewriteRecInterpolant, weqDot);
									weqTerms.add(weqTerm);
								}
							}
							// Build the nweq term for the concatenation of the outer B-paths on store and index path
							final Term concatLeft = other.mLastChange[color];
							final Term concatRight = rewriteToArray;
							final Set<Term> otherMainStores = other.mStoreIndices[color];
							final int concatStores =
									fPiAOrderForRecursion + (otherMainStores == null ? 0 : otherMainStores.size());
							final Term concatWeqTerm =
									buildWeqTerm(concatLeft, concatRight, concatStores, rewriteRecInterpolant, weqDot);
							weqTerms.add(concatWeqTerm);
							final Term weqPart = mTheory.and(weqTerms.toArray(new Term[weqTerms.size()]));
							recursiveInterpolant = mTheory.let(lastRecVar, currentRecVar, recursiveInterpolant);
							recursiveInterpolant = mTheory.and(recursiveInterpolant, pathInterpolant, weqPart);
						}
						lastRecVar = currentRecVar;
					}
				}
				// Replace the recursionVar by the first shared term
				recursiveInterpolant = mTheory.let(lastRecVar, mLastChange[color], recursiveInterpolant);
				mPathInterpolants[color].add(recursiveInterpolant);
			}
		}
	}

	/**
	 * Helper class to store the information from the store path in weakeq-ext: the shared path end arrays and all store
	 * indices on this A- or B-path.
	 */
	private class StorePath {
		final Term mLeft;
		final Term mRight;
		final Set<Term> mStores;
		final boolean mIsAPath;

		public StorePath(Term left, Term right, Set<Term> stores, boolean isAPath) {
			mLeft = left;
			mRight = right;
			mStores = stores;
			mIsAPath = isAPath;
		}
	}
}
