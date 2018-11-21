/*
 * Copyright (C) 2016-2018 University of Freiburg
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
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
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
 * Details on read-over-weakeq and weakeq-ext interpolants in our IJCAR 2018 paper.
 *
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class ArrayInterpolator {

	/* General info to set up the ArrayInterpolator */
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	private Set<Term>[] mInterpolants;

	/**
	 * Information about the lemma proof term.
	 */
	private InterpolatorClauseTermInfo mLemmaInfo;
	/**
	 * The main disequality of this lemma, i.e., "a[i]!=b[j]" for read-over-weakeq, "a!=b" for weakeq-ext, "a[i]!=v" for
	 * read-const-weakeq, "v!=w" for const-weakeq.
	 */
	private AnnotatedTerm mDiseq;
	/**
	 * The LitInfo for the main disequality of this lemma.
	 */
	private LitInfo mDiseqInfo;
	/**
	 * The atoms of the equality literals in this lemma. Note that they appear negated in the clause.
	 */
	private Map<SymmetricPair<Term>, AnnotatedTerm> mEqualities;
	/**
	 * The atoms of the disequality literals in this lemma. Note that they appear positively in the clause.
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
	 * For weakeq-ext, if there exist mixed partitions, there is one where the outer A-path is strictly longer than the
	 * outer B-path. Above (including) this partition, the B-path is used for recursion to get a smaller interpolant,
	 * hence those partitions are A-local. This occurrence has NO shared partitions.
	 */
	private Occurrence mABSwitchOccur;
	/**
	 * The strong path between the select indices of the main disequality for read-over-weakeq.
	 */
	private AnnotatedTerm mIndexEquality;
	/**
	 * This map contains the paths for weak congruence on index i in weakeq-ext.
	 */
	private Map<Term, ProofPath> mIndexPaths;
	/**
	 * Index paths in weakeq-ext that have already been interpolated.
	 */
	private Map<Term, WeakPathInfo> mIndexPathInfos;
	/**
	 * Index paths in weakeq-ext that have already been interpolated for the recursion part.
	 */
	private Map<Term, WeakPathInfo> mRecIndexPathInfos;
	/**
	 * The term on the side of the main path to which we rewrite the first shared array in mixed weakeq-ext and mixed
	 * const-weakeq.
	 */
	private Term[] mRewriteSide;
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
	 *            An array lemma.
	 * @return An array containing interpolants for all partitions.
	 */
	public Term[] computeInterpolants(final Term proofTerm) {
		mLemmaInfo = mInterpolator.getClauseTermInfo(proofTerm);
		assert mLemmaInfo.getDiseq() instanceof AnnotatedTerm;
		mDiseq = (AnnotatedTerm) mLemmaInfo.getDiseq();
		mDiseqInfo = mInterpolator.getLiteralInfo(mDiseq);
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
		} else if (mLemmaInfo.getLemmaType().equals(":weakeq-ext")) {
			interpolants = computeWeakeqExtInterpolants(proofTerm);
		} else if (mLemmaInfo.getLemmaType().equals(":const-weakeq")) {
			interpolants = computeConstWeakeqInterpolants(proofTerm);
		} else {
			assert mLemmaInfo.getLemmaType().equals(":read-const-weakeq") : "Unknown array lemma!";
			interpolants = computeReadConstWeakeqInterpolants(proofTerm);
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
	 *            A read-over-weakeq lemma.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeReadOverWeakeqInterpolants(final Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length <= 2;
		if (paths.length == 2) {
			assert paths[0].getIndex() == null;
			final Term[] indexPath = paths[0].getPath();
			assert indexPath.length == 2;
			mStorePath = paths[1];
			mIndexEquality = mEqualities.get(new SymmetricPair<Term>(indexPath[0], indexPath[1]));
		} else { // In this case, the main disequality is of form "a[i] != b[i]"
			mStorePath = paths[0];
		}

		final WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);

		determineInterpolationColor();

		// Determine the shared select index for all partitions where it exists.
		arrayPath.mSharedIndex = findSharedTerms(mStorePath.getIndex());
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
	 *            A weakeq-ext lemma.
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
			mRewriteSide = new Term[mNumInterpolants];
			mRecursionVar = mTheory.createFreshTermVariable("recursive", mStorePath.getPath()[0].getSort());
			mRecIndexPathInfos = new HashMap<Term, WeakPathInfo>();
		} else {
			// If there are no mixed partitions, we can already determine the way we interpolate. Else, we first have to
			// count for which side we need less recursion steps.
			determineInterpolationColor();
		}

		// Compute the interpolant terms starting on the store path.
		final WeakPathInfo mainPath = new WeakPathInfo(mStorePath);
		mainPath.collectStorePaths();
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
	 * Compute interpolants for a const-weakeq lemma.
	 * 
	 * It consists of a disequality "v != w" and a weak equivalence path between arrays const(v) and const(w).
	 * 
	 * @param proofTerm
	 *            a const-weakeq lemma.
	 * @return an array containing the interpolants of the lemma for all partitions of the interpolation problem.
	 */
	private Term[] computeConstWeakeqInterpolants(Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length == 1;
		mStorePath = paths[0];

		if (mDiseqInfo.getMixedVar() != null) {
			mRewriteSide = new Term[mNumInterpolants];
		} else {
			// If there are no mixed partitions, we can already determine the way we interpolate. Else, we first have to
			// count for which side we need less rewrite steps.
			determineInterpolationColor();
		}

		final WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);
		arrayPath.collectStorePaths();
		mInterpolants = arrayPath.interpolateStorePathInfoConst();

		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mABSwitchOccur.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
				interpolants[color] = mTheory.or(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			} else { // the interpolant is the conjunction of all path interpolants
				interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			}
		}

		return interpolants;
	}

	/**
	 * Compute interpolants for a read-const-weakeq lemma.
	 * 
	 * It consists of a disequality "a[i] != v" and a weak equivalence path for index i between array a and const(v).
	 * 
	 * @param proofTerm
	 *            a read-const-weakeq lemma.
	 * @return an array containing the interpolants of the lemma for all partitions of the interpolation problem.
	 */
	private Term[] computeReadConstWeakeqInterpolants(Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length == 1;
		mStorePath = paths[0];

		final WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);

		determineInterpolationColor();

		// Set the sharedIndex for all partitions where the weakpath index is shared.
		final Term weakeqIndex = mStorePath.getIndex();
		for (int color = 0; color < mNumInterpolants; color++) {
			final Occurrence indexOccur = mInterpolator.getOccurrence(weakeqIndex);
			if (indexOccur.isAB(color)) {
				arrayPath.mSharedIndex[color] = weakeqIndex;
			}
		}

		// Compute the interpolant terms from the store path
		mInterpolants = arrayPath.interpolateWeakPathInfo(true);

		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mABSwitchOccur.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
				interpolants[color] = mTheory.or(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			} else { // the interpolant is the conjunction of all path interpolants
				interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			}
		}
		return interpolants;
	}

	/**
	 * Determine how the lemma is interpolated. We say that it is 'B-interpolated' if we summarize A-paths. This
	 * counterintuitive notation results from the fact that we do this when mDiseq is in B. For mixed weakeq-ext and
	 * const-weakeq, this should be called after setting mRewriteSide.
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
		} else if (mLemmaInfo.getLemmaType().equals(":read-const-weakeq")) {
			// Compute the first partition where the select term (i.e. not the value "v" of "const(v)") is A-local.
			final InterpolatorLiteralTermInfo diseqInfo = mInterpolator.getLiteralTermInfo(mDiseq);
			final ApplicationTerm mainDiseqApp = diseqInfo.getEquality();
			final Term left = mainDiseqApp.getParameters()[0];
			final Term right = mainDiseqApp.getParameters()[1];
			final Term select;
			if (left instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals("select")) {
				select = left;
			} else {
				assert right instanceof ApplicationTerm
						&& ((ApplicationTerm) right).getFunction().getName().equals("select");
				select = right;
			}
			// Compute the first partition where select is A-local.
			final Occurrence selectInfo = mInterpolator.getOccurrence(select);
			while (true) {
				final int child = getChild(color, selectInfo);
				if (child < 0) {
					break;
				}
				assert selectInfo.isALocal(child);
				color = child;
			}
		} else {
			// Find the first mixed partition where the shorter outer path is the A-path.
			color = 0;
			while (!mDiseqInfo.isALocal(color)) {
				if (mDiseqInfo.isMixed(color)) {
					assert mRewriteSide[color] != null; // Must be set before we can determine interpolation color.
					final Occurrence rewriteInfo = mInterpolator.getOccurrence(mRewriteSide[color]);
					if (rewriteInfo.isALocal(color)) {
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
		// All partitions above (and including) the computed color have to be interpolated as if mDiseq was A-local
		mABSwitchOccur.occursIn(color);
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

	private static boolean isConstArray(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("const");
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

	private static Term getValueFromConst(final Term constArr) {
		assert isConstArray(constArr);
		return ((ApplicationTerm) constArr).getParameters()[0];
	}

	private Term buildConst(final Term value, final Sort arraySort) {
		FunctionSymbol fsym = mTheory.getFunctionWithResult("const", null, arraySort, value.getSort());
		return mTheory.term(fsym, value);
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
		final Term leftSelect = buildSelect(left, index);
		final Term rightSelect = buildSelect(right, index);
		return mTheory.equals(leftSelect, rightSelect);
	}

	/**
	 * Build a select term from a term and an index term.
	 * 
	 * @param term
	 *            can be (i) an array term "a", (ii) a constant array "const(v)", (iii) a mixed select equality
	 *            "a[i]=b[j]".
	 * @param index
	 *            an index term "i"
	 * @return in case (i) a select term "a[i]", in case (ii) "v", in case (iii) the mixed variable
	 */
	private Term buildSelect(final Term term, final Term index) {
		final Term select;
		if (term instanceof AnnotatedTerm && (mEqualities.containsValue(term) || term.equals(mDiseq))) {
			// The term is actually a mixed select equality
			final LitInfo selectInfo = mInterpolator.getLiteralInfo(term);
			select = selectInfo.getMixedVar();
		} else if (isConstArray(term)) {
			select = getValueFromConst(term);
		} else {
			select = mTheory.term("select", term, index);
		}
		return select;
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
			rewrite = mTheory.term("store", rewrite, diffTerm, buildSelect(right, diffTerm));
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
			rewrite = mTheory.term("store", rewrite, diffTerm, buildSelect(right, diffTerm));
		}
		nweqTerm = mTheory.or(nweqTerm, mTheory.not(mTheory.equals(rewrite, right)));

		return nweqTerm;
	}

	/**
	 * For mixed const-weakeq and read-const-weakeq, build the interpolant clause for the outer path ending with a
	 * constant array.
	 * 
	 * Particularity: We do not have a shared term for the constant array at the path end, neither the constant value.
	 * But we can get the constant value from the last shared array as it must store it almost everywhere because of the
	 * weak equivalence.
	 *
	 * @param isAPath
	 *            set to true if the path is an A path
	 * @param sharedArr
	 *            the shared array from which the constant array is built
	 * @param sharedIndices
	 *            the shared store indices on the path
	 * @param auxVar
	 *            the variable to build the weq or nweq term
	 * @param order
	 *            the order of the weq term (and order-1 rewrite steps to search for the value)
	 * @param fPi
	 *            the formula satisfied by the diff terms, with an auxiliary variable
	 * @return
	 */
	private Term buildConstPathInterpolant(final boolean isAPath, final Term sharedArr, final Set<Term> sharedIndices,
			final TermVariable auxVar, final int order, final Term fPi) {

		// Build the interpolant conjuncts (B-path) or disjuncts (A-path) with a dummy for the correct value.
		final TermVariable vTilde = mTheory.createFreshTermVariable("vTilde", mDiseqInfo.getMixedVar().getSort());
		final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), vTilde);
		final Term itpClause;
		if (isAPath) {
			itpClause = buildWeqTerm(buildConst(vTilde, sharedArr.getSort()), sharedArr, order, fPi, auxVar);
		} else {
			itpClause = buildNweqTerm(buildConst(vTilde, sharedArr.getSort()), sharedArr, order, fPi, auxVar);
		}
		final Term itpVTilde = isAPath ? mTheory.and(eqTerm, itpClause) : mTheory.or(eqTerm, itpClause);

		// Search for the correct value to construct a constant array that is equal to the one at the path end.
		// Start with a random value in sharedArr. The constant array built from this value is either the correct
		// constant array, or can be used to find the constant value in < n=order diff steps with sharedArr, after
		// rewriting it towards sharedArr at sharedIndices.
		Term searchIdx = mTheory.term("@diff", sharedArr, sharedArr);
		Term searchVal = buildSelect(sharedArr, searchIdx);
		Term searchArr = buildConst(searchVal, sharedArr.getSort());
		for (final Term idx : sharedIndices) {
			searchArr = mTheory.term("store", searchArr, idx, buildSelect(sharedArr, idx));
		}
		Term constPathItp = mTheory.let(vTilde, searchVal, itpVTilde);
		for (int i = 0; i < order; i++) {
			searchIdx = mTheory.term("@diff", searchArr, sharedArr);
			searchVal = buildSelect(sharedArr, searchIdx);
			if (isAPath) {
				constPathItp = mTheory.or(constPathItp, mTheory.let(vTilde, searchVal, itpVTilde));
			} else {
				constPathItp = mTheory.and(constPathItp, mTheory.let(vTilde, searchVal, itpVTilde));
			}
			searchArr = mTheory.term("store", searchArr, searchIdx, buildSelect(sharedArr, searchIdx));
		}
		return constPathItp;
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
		/**
		 * The store indices in the order they appear on the main path in weakeq-ext. An index can appear several times.
		 * In mixed weakeq-ext, we might have to build both the "normal" and the "dual" subinterpolant for recursion.
		 */
		private Vector<Term> mStores;
		/**
		 * The A- and B-paths on the main path in weakeq-ext.
		 */
		private Vector<StorePath>[] mStorePaths;

		@SuppressWarnings("unchecked")
		public WeakPathInfo(final ProofPath path) {
			mPathIndex = path.getIndex();
			mSharedIndex = new Term[mNumInterpolants];
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
		 * Compute the interpolants for this weakpath for read-over-weakeq, for read-const-weakeq, or for the index
		 * paths of weakeq-ext.
		 * 
		 * @param close
		 *            set to false to get the interpolant of the inner paths only (for recursion in mixed weakeq-ext)
		 * @return An array containing the interpolant terms for this weakpath for each partition.
		 */
		public Set<Term>[] interpolateWeakPathInfo(boolean close) {
			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			// Determine whether to start and end with A or B or AB.
			final Term headTerm, tailTerm;
			final String lemmaType = mLemmaInfo.getLemmaType();
			if (lemmaType.equals(":read-over-weakeq") || lemmaType.equals(":read-const-weakeq")) {
				// The select or value term of the main diseq corresponding to the left path end determines start color.
				final InterpolatorLiteralTermInfo diseqInfo = mInterpolator.getLiteralTermInfo(mDiseq);
				final Term[] diseqTerms = diseqInfo.getEquality().getParameters();
				if (isSelectTerm(diseqTerms[0]) && getArrayFromSelect(diseqTerms[0]).equals(mPath[0])
						|| isConstArray(mPath[0]) && getValueFromConst(mPath[0]).equals(diseqTerms[0])) {
					headTerm = diseqTerms[0];
					tailTerm = diseqTerms[1];
				} else {
					headTerm = diseqTerms[1];
					tailTerm = diseqTerms[0];
				}
			} else {
				assert lemmaType.equals(":weakeq-ext");
				// The left path end (equal to one side of the main diseq) determines start color.
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
							final Term leftTerm = selectEqApp.getParameters()[0];
							final Term rightTerm = selectEqApp.getParameters()[1];

							Term leftSelect = null;
							Term rightSelect = null;
							if (isSelectTerm(leftTerm)) {
								if (getArrayFromSelect(leftTerm).equals(left)) {
									leftSelect = leftTerm;
								} else {
									assert getArrayFromSelect(leftTerm).equals(right);
									rightSelect = leftTerm;
								}
							}
							if (isSelectTerm(rightTerm)) {
								if (getArrayFromSelect(rightTerm).equals(left)) {
									assert leftSelect == null;
									leftSelect = rightTerm;
								} else {
									assert getArrayFromSelect(rightTerm).equals(right) && rightSelect == null;
									rightSelect = rightTerm;
								}
							}

							// Add the index equality for the first select term (if it is a select)
							mTail.closeAPath(mHead, boundaryTerm, stepInfo);
							mTail.openAPath(mHead, boundaryTerm, stepInfo);
							if (leftSelect != null) {
								mTail.addSelectIndexEquality(mHead, leftSelect);
							}
							// If the equality is mixed in some partition, we open or close the path at the mixed
							// variable, storing the mixed equality as boundary term.
							final TermVariable mixedVar = stepInfo.getMixedVar();
							if (mixedVar != null) {
								final Occurrence rightOcc;
								if (rightSelect != null) {
									rightOcc = mInterpolator.getOccurrence(rightSelect);
								} else {
									assert isConstArray(right) && getValueFromConst(right).equals(rightTerm);
									rightOcc = mInterpolator.getOccurrence(rightTerm);
								}
								if (leftSelect != null && rightSelect != null) {
									boundaryTerm = selectEq;
								} else { // It is a const select equality - we close the path with const(mixedVar)
									boundaryTerm = buildConst(mixedVar, left.getSort());
								}
								mTail.closeAPath(mHead, boundaryTerm, rightOcc);
								mTail.openAPath(mHead, boundaryTerm, rightOcc);
							}
							// The other index equality is added after opening/closing (if the rightTerm is a select)
							if (rightSelect != null) {
								mTail.addSelectIndexEquality(mHead, rightSelect);
							}
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
						mTail.addIndexDisequality(mHead, indexDiseq);

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
			if (close) { // ... unless we compute the "dual" interpolant for recursion in mixed weakeq-ext
				addDiseq(headOccur, tailOccur);
				closeWeakPath();
			} else {
				closeWeakPath();
			}
			return mPathInterpolants;
		}

		/**
		 * Collect the store paths for the weak equivalence path in weakeq-ext and const-weakeq.
		 */
		@SuppressWarnings("unchecked")
		public void collectStorePaths() {
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
					mTail.addMainStoreIndex(mHead, storeIndex);
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
							mRewriteSide[color] = mPath[0];
						} else {
							mRewriteSide[color] = mPath[mPath.length - 1];
						}
					}
				}
				determineInterpolationColor();
			}
		}

		/**
		 * Interpolate the main path of weakeq-ext for all partitions. This also computes the subinterpolants for the
		 * index paths.
		 */
		public Set<Term>[] interpolateStorePathInfoExt() {
			assert mStorePaths != null;
			// Build all subinterpolants
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
					if (mDiseqInfo.isMixed(color) && mRewriteSide[color] == mPath[0] && storePath.mLeft == null
							|| mDiseqInfo.isMixed(color) && mRewriteSide[color] == mPath[mPath.length - 1]
									&& storePath.mRight == null) {
						recursionPath = storePath;
					} else {
						mTail.addInterpolantClauseExt(color, storePath);
					}
				}
				if (mDiseqInfo.isMixed(color)) {
					final WeakPathEnd recSide = mRewriteSide[color] == mPath[0] ? mHead : mTail;
					final WeakPathEnd other = recSide == mHead ? mTail : mHead;
					recSide.buildRecursiveInterpolant(color, other, recursionPath);
				}
			}

			return mPathInterpolants;
		}

		/**
		 * Interpolate the weak equivalence path for const-weakeq.
		 */
		public Set<Term>[] interpolateStorePathInfoConst() {
			assert mStorePaths != null;
			for (int color = 0; color < mNumInterpolants; color++) {
				final boolean collectA = !mABSwitchOccur.isALocal(color);
				for (StorePath storePath : mStorePaths[color]) {
					// Collect shared indices to rewrite and shorten the path
					final Set<Term> sharedIndices = new HashSet<Term>();
					int order = 0;
					if (storePath.mStores != null) {
						order = storePath.mStores.size();
						for (final Term idx : storePath.mStores) {
							final Occurrence occur = mInterpolator.getOccurrence(idx);
							if (occur.isAB(color)) {
								sharedIndices.add(idx);
								order--;
							}
						}
					}
					final Term itpClause;
					final TermVariable cdot = order == 0 ? null
							: mTheory.createFreshTermVariable("cdot", storePath.mStores.iterator().next().getSort());

					if (storePath.mLeft != null && storePath.mRight != null) { // Inner path
						Term rewriteLeftAtShared = storePath.mLeft;
						for (final Term idx : sharedIndices) {
							rewriteLeftAtShared =
									mTheory.term("store", rewriteLeftAtShared, idx, buildSelect(storePath.mRight, idx));
						}
						if (storePath.mIsAPath && collectA) {
							itpClause = buildWeqTerm(rewriteLeftAtShared, storePath.mRight, order, mTheory.mTrue, cdot);
							mPathInterpolants[color].add(itpClause);
						} else if (!storePath.mIsAPath && !collectA) {
							itpClause =
									buildNweqTerm(rewriteLeftAtShared, storePath.mRight, order, mTheory.mFalse, cdot);
							mPathInterpolants[color].add(itpClause);
						}
					} else { // Outer path in the mixed case
						if (storePath.mIsAPath && collectA || !storePath.mIsAPath && !collectA) {
							final Term sharedArr = storePath.mLeft != null ? storePath.mLeft : storePath.mRight;
							assert sharedArr != null;
							final Term fPi = storePath.mIsAPath ? mTheory.mTrue : mTheory.mFalse;
							itpClause = buildConstPathInterpolant(storePath.mIsAPath, sharedArr, sharedIndices, cdot,
									order, fPi);
							mPathInterpolants[color].add(itpClause);
						}
					}
				}
			}
			return mPathInterpolants;
		}

		/**
		 * For a step in an index path of a weakeq-ext lemma that is not an array equality, check if we can find a
		 * select equality between the arrays and corresponding index equalities.
		 * 
		 * In the presence of constant arrays, one side of the select equality can be the value "v" of a "const(v)".
		 *
		 * @return the select equality if it exists, else null.
		 */
		private AnnotatedTerm findSelectEquality(final Term leftArray, final Term rightArray) {
			final SymmetricPair<Term> arrayPair = new SymmetricPair<Term>(leftArray, rightArray);
			for (final SymmetricPair<Term> testEq : mEqualities.keySet()) {
				// Find some select equality.
				final Term testLeft = testEq.getFirst();
				final Term testRight = testEq.getSecond();
				final Term leftSelect = isSelectTerm(testLeft) ? testLeft : null;
				final Term rightSelect = isSelectTerm(testRight) ? testRight : null;
				if (leftSelect != null && rightSelect != null) { // Check equalities of the form "arr1[j1] = arr2[j2]".
					// Check if the arrays of the select terms match the term pair.
					final Term testLeftArray = getArrayFromSelect(leftSelect);
					final Term testRightArray = getArrayFromSelect(rightSelect);
					final SymmetricPair<Term> testArrayPair = new SymmetricPair<Term>(testLeftArray, testRightArray);
					if (arrayPair.equals(testArrayPair)) {
						// Check if the select indices equal the weakpath index (trivially or by an equality literal).
						final Term testLeftIndex = getIndexFromSelect(leftSelect);
						final Term testRightIndex = getIndexFromSelect(rightSelect);
						if (testLeftIndex == mPathIndex
								|| mEqualities.containsKey(new SymmetricPair<Term>(testLeftIndex, mPathIndex))) {
							if (testRightIndex == mPathIndex
									|| mEqualities.containsKey(new SymmetricPair<Term>(testRightIndex, mPathIndex))) {
								return mEqualities.get(testEq);
							}
						}
					}
				} else { // Check equalities of the form "arr[j] = v".
					Term singleSelect = null;
					Term value = null;
					if (leftSelect != null) {
						singleSelect = leftSelect;
						value = testRight;
					} else if (rightSelect != null) {
						singleSelect = rightSelect;
						value = testLeft;
					}
					if (singleSelect != null) {
						final Term testArray = getArrayFromSelect(singleSelect);
						Term constArray = null;
						if (testArray.equals(leftArray) && isConstArray(rightArray)) {
							constArray = rightArray;
						} else if (testArray.equals(rightArray) && isConstArray(leftArray)) {
							constArray = leftArray;
						}
						if (constArray != null) { // The select array matches, the other array is a constant array.
							// Check that the constant array matches the value "v" of "arr[j] = v".
							if (getValueFromConst(constArray).equals(value)) {
								// Check that index "j" is equal to the path index.
								final Term testIndex = getIndexFromSelect(singleSelect);
								if (testIndex == mPathIndex
										|| mEqualities.containsKey(new SymmetricPair<Term>(testIndex, mPathIndex))) {
									return mEqualities.get(testEq);
								}
							}
						}
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
				mTail.closeAPath(mHead, boundaryTailTerm, mABSwitchOccur);
				mTail.openAPath(mHead, boundaryTailTerm, mABSwitchOccur);
				mHead.closeAPath(mTail, boundaryHeadTerm, mABSwitchOccur);
				mHead.openAPath(mTail, boundaryHeadTerm, mABSwitchOccur);
			} else {
				mTail.closeAPath(mHead, boundaryTailTerm, tailOcc);
				mTail.openAPath(mHead, boundaryTailTerm, tailOcc);
				mTail.closeAPath(mHead, boundaryTailTerm, mDiseqInfo);
				mTail.openAPath(mHead, boundaryTailTerm, mDiseqInfo);
				mHead.closeAPath(mTail, boundaryHeadTerm, headOcc);
				mHead.openAPath(mTail, boundaryHeadTerm, headOcc);
				mHead.closeAPath(mTail, boundaryHeadTerm, mDiseqInfo);
				mHead.openAPath(mTail, boundaryHeadTerm, mDiseqInfo);

				if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
					if (mIndexEquality != null) {
						final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
						mTail.addSelectIndexEqAllColors(mHead, indexEqInfo, mIndexEquality);
					}

					mTail.closeAPath(mHead, mDiseq, headOcc);
					mHead.closeAPath(mTail, mDiseq, tailOcc);
				} else if (mLemmaInfo.getLemmaType().equals(":read-const-weakeq")
						|| mLemmaInfo.getLemmaType().equals(":const-weakeq")) {
					mTail.closeAPath(mHead, mDiseq, mABSwitchOccur);
					mTail.openAPath(mHead, mDiseq, mABSwitchOccur);
					mHead.closeAPath(mTail, mDiseq, mABSwitchOccur);
					mHead.openAPath(mTail, mDiseq, mABSwitchOccur);
				} else {
					if (mPathIndex != null) { // On the store path of ext, we need to handle the mixed case separately
						mTail.closeAPath(mHead, mRecursionVar, mABSwitchOccur);
						mTail.openAPath(mHead, mRecursionVar, mABSwitchOccur);
						mHead.closeAPath(mTail, mRecursionVar, mABSwitchOccur);
						mHead.openAPath(mTail, mRecursionVar, mABSwitchOccur);
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
					assert mDiseqInfo.isALocal(color) || !mLemmaInfo.getLemmaType().equals(":read-over-weakeq");
					// A-local outer paths must be closed here, B-local ones are already closed.
					if (mHead.mTerm[color] != null) {
						mHead.addInterpolantClausePathSeg(true, color, null);
					}
					if (mTail.mTerm[color] != null) {
						mTail.addInterpolantClausePathSeg(true, color, null);
					}
					// The whole path and the diseq are in A, but there can still be B index(dis)eqs
					if (mHead.mLastChange[color] == null && mTail.mLastChange[color] == null) {
						// In this case, they are stored in mHead
						mHead.addInterpolantClausePathSeg(true, color, null);
					}
				} else {
					// B-local paths must be closed, A-local ones are already closed.
					if (mHead.mLastChange[color] != mHead.mTerm[color]) {
						mHead.addInterpolantClausePathSeg(false, color, null);
					}
					if (mTail.mLastChange[color] != mTail.mTerm[color]) {
						mTail.addInterpolantClausePathSeg(false, color, null);
					}
					// The whole path and the diseq are in B, but there can still be A index(dis)eqs
					if (mHead.mLastChange[color] == null && mTail.mLastChange[color] == null) {
						// In this case, they are stored in mHead
						mHead.addInterpolantClausePathSeg(false, color, null);
					}
				}
			}
		}

		/**
		 * Close the store path of a weakeq-ext lemma.
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
						mHead.addStorePathExt(true, color, null);
					}
					if (mTail.mTerm[color] != mPath[mPath.length - 1]) {
						mTail.addStorePathExt(true, color, null);
					}
				} else if (mDiseqInfo.isBorShared(color)) {
					// B-local outer paths must be closed, A-local ones are already closed.
					if (mHead.mLastChange[color] != mPath[0]) {
						mHead.addStorePathExt(false, color, null);
					}
					if (mTail.mLastChange[color] != mPath[mPath.length - 1]) {
						mTail.addStorePathExt(false, color, null);
					}
				} else {
					if (headOcc.isALocal(color)) {
						if (mHead.mTerm[color] != mPath[0]) {
							mHead.addStorePathExt(true, color, null);
						}
						if (mTail.mTerm[color] != mPath[mPath.length - 1]) {
							mTail.addStorePathExt(false, color, null);
						}
					} else {
						if (mHead.mLastChange[color] != mPath[0]) {
							mHead.addStorePathExt(false, color, null);
						}
						if (mTail.mLastChange[color] != mPath[mPath.length - 1]) {
							mTail.addStorePathExt(true, color, null);
						}
					}
				}
			}
		}

		/**
		 * Build the F_pi^A or F_pi^B - term. On A-paths, it collects the negated B-projections of B-local and mixed
		 * index equalities and disequalities; on B-paths, the A-projections of A-local and mixed index equalities.
		 * 
		 * @param isAPath
		 *            true if the path is an A-path, false otherwise.
		 * @param color
		 *            the current partition
		 * @param sharedIndex
		 *            the shared term representing the weakpathindex
		 * @param indexDiseqs
		 *            disequalities between weakpathindex and indices of store terms on the path
		 * @param indexEqs
		 *            equalities between weakpathindex and indices of select eqs on the path
		 * @return for A-paths, the disjunction of the negated B-projections of index diseqs and eqs, in shared terms,
		 *         for B-paths the conjunction of the A-projections of index diseqs and eqs, in shared terms.
		 * 
		 */
		private Term buildFPiTerm(final boolean isAPath, final int color, final Term sharedIndex,
				final ArrayList<AnnotatedTerm> indexDiseqs, final ArrayList<AnnotatedTerm> indexEqs) {
			if (indexDiseqs == null && indexEqs == null) {
				return isAPath ? mTheory.mFalse : mTheory.mTrue;
			}

			final Set<Term> indexTerms = new HashSet<Term>();
			if (indexDiseqs != null) {
				for (final AnnotatedTerm diseq : indexDiseqs) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(diseq);
					final LitInfo info = mInterpolator.getLiteralInfo(diseq);
					final ApplicationTerm diseqApp = termInfo.getEquality();
					// Collected index diseqs are either mixed or B-local on A-paths (resp. A-local on B-paths).
					// In the first case, there is a mixed term, in the second, the store index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: diseqApp.getParameters()[0].equals(mPathIndex) ? diseqApp.getParameters()[1]
									: diseqApp.getParameters()[0];
					// On A-paths, the negated B-projection of the index diseq is added.
					// It is always an equality (representing an EQ term for mixed index diseqs).
					Term projection = mTheory.equals(index, sharedIndex);
					// On B-paths, the A-projection of the index diseq is added.
					// It is an equality (EQ-term) for mixed index diseq, and a disequality for A-local index diseq.
					if (!isAPath && info.isALocal(color)) {
						projection = mTheory.not(projection);
					}
					indexTerms.add(projection);
				}
			}
			if (indexEqs != null) {
				for (final AnnotatedTerm eq : indexEqs) {
					final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(eq);
					final LitInfo info = mInterpolator.getLiteralInfo(eq);
					final ApplicationTerm eqApp = termInfo.getEquality();
					// Index eqs are either mixed or B-local on A-paths (resp. A-local on B-paths).
					// In the first case, there is a mixed term, in the second, the select index is shared.
					final Term index = info.isMixed(color) ? info.getMixedVar()
							: eqApp.getParameters()[0].equals(mPathIndex) ? eqApp.getParameters()[1]
									: eqApp.getParameters()[0];
					// On B-paths, the A-projection is added. It is always an equality.
					Term projection = mTheory.equals(index, sharedIndex);
					// On A-paths, the negated B-projection is added. It is always a disequality.
					if (isAPath) {
						projection = mTheory.not(projection);
					}
					indexTerms.add(projection);
				}
			}

			final Term fPiTerm;
			if (isAPath) {
				fPiTerm = mTheory.or(indexTerms.toArray(new Term[indexTerms.size()]));
			} else {
				fPiTerm = mTheory.and(indexTerms.toArray(new Term[indexTerms.size()]));
			}
			return fPiTerm;
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
			ArrayList<AnnotatedTerm>[] mIndexDiseqs;
			/**
			 * For each partition this contains the set of B(resp. A)-local and mixed select index equalities found on
			 * the A (resp. B) path so far.
			 */
			ArrayList<AnnotatedTerm>[] mIndexEqs;
			/**
			 * For each partition, this stores the store indices on the A (B) path so far. This is only used for the
			 * main path of a weakeq-ext lemma.
			 */
			Set<Term>[] mMainStores;

			@SuppressWarnings("unchecked")
			public WeakPathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
				mLastChange = new Term[mNumInterpolants];
				if (mPathIndex != null) {
					mIndexDiseqs = new ArrayList[mNumInterpolants];
					mIndexEqs = new ArrayList[mNumInterpolants];
				} else { // the path is the store path of a weakeq-ext lemma
					mMainStores = new Set[mNumInterpolants];
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
						addInterpolantClausePathSeg(true, color, boundary);
					} else { // Store path in weakeq-ext lemma
						addStorePathExt(true, color, boundary);
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
							addInterpolantClausePathSeg(false, child, boundary);
						} else { // we are on the store path in a weakeq-ext lemma
							addStorePathExt(false, child, boundary);
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
			private void addIndexDisequality(final WeakPathEnd other, final AnnotatedTerm diseq) {
				final LitInfo diseqInfo = mInterpolator.getLiteralInfo(diseq);

				// The diseq has to be added to all partitions where it is mixed and all partitions that lie on the
				// tree path between the partition of the diseq and the partition of the store term.
				// In nodes under the lca which are not on the way, both are in B, in nodes above the lca both are in A,
				// and in both cases there is nothing to do.
				addIndexDiseqAllColors(other, diseqInfo, diseq);
				if (diseqInfo.getMixedVar() != null) {
					// Additionally go up and down with weakpathindexoccur
					final Occurrence occur = mInterpolator.getOccurrence(mPathIndex);
					addIndexDiseqAllColors(other, occur, diseq);
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index disequality to
			 * those partitions. This adds the index disequality to all partitions where it is not in A (resp. B) while
			 * the path is.
			 */
			private void addIndexDiseqAllColors(final WeakPathEnd other, final Occurrence occur,
					final AnnotatedTerm diseq) {
				int currentColor = mColor;
				// Up
				mHasABPath.and(occur.mInA);
				while (currentColor < mNumInterpolants && occur.isBLocal(currentColor)) {
					assert mHasABPath.isEmpty();
					final int color = currentColor;
					currentColor = getParent(color);
					addIndexDiseqOneColor(other, diseq, color);
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
						addIndexDiseqOneColor(other, diseq, child);
						currentColor = child;
					}
				}
			}

			/**
			 * Add the index disequality to one partition.
			 */
			private void addIndexDiseqOneColor(final WeakPathEnd other, final AnnotatedTerm diseq, final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexDiseqs[color] == null) {
						other.mIndexDiseqs[color] = new ArrayList<AnnotatedTerm>();
					}
					other.mIndexDiseqs[color].add(diseq);
				} else { // Else in this one.
					if (mIndexDiseqs[color] == null) {
						mIndexDiseqs[color] = new ArrayList<AnnotatedTerm>();
					}
					mIndexDiseqs[color].add(diseq);
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
					addSelectIndexEqAllColors(other, eqInfo, indexEq);
					if (eqInfo.getMixedVar() != null) {
						final Occurrence occur = mInterpolator.getOccurrence(mPathIndex);
						addSelectIndexEqAllColors(other, occur, indexEq);
					}
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index equality to
			 * those partitions. This adds the index equality to all partitions where it is not in A (resp. B) while the
			 * path is.
			 */
			private void addSelectIndexEqAllColors(final WeakPathEnd other, final Occurrence occur,
					final AnnotatedTerm eq) {
				int currentColor = mColor;
				// Up
				mHasABPath.and(occur.mInA);
				while (currentColor < mNumInterpolants && occur.isBLocal(currentColor)) {
					assert mHasABPath.isEmpty();
					final int color = currentColor;
					currentColor = getParent(color);
					addSelectIndexEqOneColor(other, eq, color);
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
						addSelectIndexEqOneColor(other, eq, child);
						currentColor = child;
					}
				}
			}

			/**
			 * Add the index equality to one partition.
			 */
			private void addSelectIndexEqOneColor(final WeakPathEnd other, final AnnotatedTerm eq, final int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexEqs[color] == null) {
						other.mIndexEqs[color] = new ArrayList<AnnotatedTerm>();
					}
					other.mIndexEqs[color].add(eq);
				} else { // Else in this one.
					if (mIndexEqs[color] == null) {
						mIndexEqs[color] = new ArrayList<AnnotatedTerm>();
					}
					mIndexEqs[color].add(eq);
				}
			}

			/**
			 * Add the store index of a store step in the main path of weakeq-ext.
			 *
			 * @param other
			 *            the other path end.
			 * @param storeIndex
			 *            the store index.
			 */
			private void addMainStoreIndex(final WeakPathEnd other, final Term storeIndex) {
				for (int color = 0; color < mNumInterpolants; color++) {
					// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null,
					// we have to store the diseq in the other pathend
					if (other.mLastChange[color] == null) {
						if (other.mMainStores[color] == null) {
							other.mMainStores[color] = new HashSet<Term>();
						}
						other.mMainStores[color].add(storeIndex);
					} else { // else in this one.
						if (mMainStores[color] == null) {
							mMainStores[color] = new HashSet<Term>();
						}
						mMainStores[color].add(storeIndex);
					}
				}
			}

			/**
			 * Add an interpolant clause for a closed A or B path segment.
			 * 
			 * If we collect A-paths, and there is a shared index (case 4.1), A-paths are summarized by a conjunct of
			 * the form "i!=k1/\.../\i!=kn->start[i]=end[i]", i.e. the conjunction of all B-local or the B-part of mixed
			 * index diseqs on this path is a premise for the arrays at the path ends to coincide at weakpathindex. For
			 * B-paths, the A-projections of A-local and mixed index disequalities are added as conjunct to the entire
			 * lemma interpolant. If there is no shared index (case 4.3), weq terms are built stating that the arrays at
			 * the path ends differ at most at k locations (k= # of B-local and mixed index diseqs on the path) which
			 * are all different from weakpathindex. For B-paths there is nothing to do in this case.
			 * 
			 * Analogously, if we collect B-paths and there is a shared index (case 4.2), B-paths are summarized by a
			 * disjunct of the form "i!=k1/\.../\i!=kn/\start[i]!=end[i]". For A-paths, the B-projections of B-local and
			 * mixed index disequalities are added as disjunct to the entire lemma interpolant. If there is no shared
			 * index (case 4.4), an nweq term is built stating that the arrays at the path ends differ at least at k
			 * locations (k= # A-local and mixed index diseqs on the path) of which (at least) one equals the
			 * weakpathindex. For A-paths, there is nothing to do.
			 * 
			 * @param isAPath
			 *            true if the path is an A-path, false otherwise.
			 * @param color
			 *            the current partition
			 * @param boundary
			 *            the term which closed the path segment
			 */
			private void addInterpolantClausePathSeg(final boolean isAPath, final int color, final Term boundary) {
				final boolean collectA = !mABSwitchOccur.isALocal(color); // For better readability.

				final Term left = mLastChange[color];
				final Term right = boundary;

				if (mSharedIndex[color] != null) { // Cases 4.1 and 4.2
					final Term index = mSharedIndex[color];
					final Term fPi = buildFPiTerm(isAPath, color, index, mIndexDiseqs[color], mIndexEqs[color]);
					mIndexDiseqs[color] = null;
					mIndexEqs[color] = null;

					if (collectA && isAPath || !collectA && !isAPath) { // Select terms and F_pi terms are needed.
						final Term selectEq = buildSelectEq(left, right, index);
						final Term itpClause;
						if (collectA) { // Case 4.1
							itpClause = mTheory.or(selectEq, fPi);
						} else { // Case 4.2
							itpClause = mTheory.and(mTheory.not(selectEq), fPi);
						}
						mPathInterpolants[color].add(itpClause);
					} else { // Only F_pi terms are added
						if (isAPath && !(fPi.equals(mTheory.mFalse))) {
							assert mSharedIndex[color] == mPathIndex || mLemmaInfo.getLemmaType().equals(":weakeq-ext");
						}
						mPathInterpolants[color].add(fPi); // Cases 4.1 and 4.2
					}

				} else if (collectA && isAPath || !collectA && !isAPath) { // A-paths for case 4.3, B-paths for 4.4.
					// Use shared store indices to rewrite "left" to "right" in order to shorten the weq- or nweq-term.
					Set<Term> sharedIndices = new HashSet<Term>();
					if (mIndexDiseqs[color] != null) {
						Iterator<AnnotatedTerm> it = mIndexDiseqs[color].iterator();
						while (it.hasNext()) {
							final AnnotatedTerm diseq = it.next();
							final InterpolatorLiteralTermInfo termInfo = mInterpolator.getLiteralTermInfo(diseq);
							final LitInfo info = mInterpolator.getLiteralInfo(diseq);
							if (!info.isMixed(color)) {
								final ApplicationTerm diseqApp = termInfo.getEquality();
								final Term storeIndex =
										diseqApp.getParameters()[0].equals(mPathIndex) ? diseqApp.getParameters()[1]
												: diseqApp.getParameters()[0];
								final Occurrence storeOcc = mInterpolator.getOccurrence(storeIndex);
								if (storeOcc.isAB(color)) {
									sharedIndices.add(storeIndex);
									it.remove();
								}
							}
						}
					}
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final Term itpClause;
					if (mLemmaInfo.getLemmaType().equals(":read-const-weakeq") && boundary.equals(mDiseq)) {
						// This is the outer path ending with a const array in mixed read-const-weakeq
						final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
						final Term fPi = buildFPiTerm(isAPath, color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
						mIndexDiseqs[color] = null;
						mIndexEqs[color] = null;
						itpClause = buildConstPathInterpolant(isAPath, left, sharedIndices, cdot, order, fPi);
					} else {
						Term rewriteLeftAtShared = left;
						for (final Term idx : sharedIndices) {
							rewriteLeftAtShared =
									mTheory.term("store", rewriteLeftAtShared, idx, buildSelect(right, idx));
						}
						final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
						final Term fPi = buildFPiTerm(isAPath, color, cdot, mIndexDiseqs[color], mIndexEqs[color]);
						mIndexDiseqs[color] = null;
						mIndexEqs[color] = null;

						if (isAPath) {
							itpClause = buildWeqTerm(rewriteLeftAtShared, right, order, fPi, cdot);
						} else {
							itpClause = buildNweqTerm(rewriteLeftAtShared, right, order, fPi, cdot);
						}
					}
					mPathInterpolants[color].add(itpClause);

				} else { // Nothing to do for A-paths in case 4.3 and for B-paths in case 4.4.
					// In read-over-weakeq without shared index, if the select index is A-local, there cannot be B-local
					// or mixed disequalities on A-paths (and similarly for B-paths)
					if (mLemmaInfo.getLemmaType().equals(":read-over-weakeq")) {
						assert mIndexDiseqs[color] == null;
					} else { // Can happen when recursive interpolant is built
						assert mIndexDiseqs[color] == null || !mDiseqInfo.isMixed(color);
					}
				}
			}

			/**
			 * Add an A or B store path to the main path in weakeq-ext. This stores all the information that is needed
			 * to compute the interpolant terms once we have traversed the whole main path and computed all
			 * sub-interpolants.
			 * 
			 * @param isAPath
			 *            true if the path is an A path, false otherwise
			 * @param color
			 *            the current partition
			 * @param boundary
			 *            the array term that closed the path
			 */
			private void addStorePathExt(final boolean isAPath, final int color, final Term boundary) {
				final Term left, right;
				if (this.equals(mTail)) {
					left = mLastChange[color];
					right = boundary;
				} else { // This is needed when we close the left outer paths.
					left = boundary;
					right = mLastChange[color];
				}
				final Set<Term> stores = mMainStores[color];
				final StorePath storePath = new StorePath(left, right, stores, isAPath);
				if (this.equals(mTail)) {
					mStorePaths[color].add(storePath);
				} else { // This is the left outer path
					mStorePaths[color].add(0, storePath);
				}
				if (left != null && right != null) {
					// Keep the store indices on the outer paths to build the recursive interpolant in closeWeakeqExt.
					mMainStores[color] = null;
				}
			}

			/**
			 * Add the interpolant clause for a store path in weakeq-ext.
			 * 
			 * If we collect A-paths (case 5.1 and 5.3), A-paths are summarized by weq terms containing the interpolants
			 * for the weak congruence paths for the store indices on this path. For B-paths, the interpolants for the
			 * corresponding weak congruences are added as conjuncts to the entire lemma interpolant.
			 * 
			 * Analogously, if we collect B-paths (case 5.2 and 5.3 optimized), B-paths are summarized by nweq terms
			 * containing the interpolants for the weak congruence paths for the store indices on this path. For
			 * B-paths, the interpolants for the corresponding weak congruences are added as disjuncts to the entire
			 * lemma interpolant.
			 * 
			 * @param color
			 *            The current partition.
			 * @param storePath
			 *            The A or B store path on the main path.
			 */
			private void addInterpolantClauseExt(final int color, final StorePath storePath) {
				final boolean isAPath = storePath.mIsAPath;
				final boolean collectA = !mABSwitchOccur.isALocal(color); // For readability

				if (collectA && isAPath || !collectA && !isAPath) {
					final Term left = storePath.mLeft;
					final Term right = storePath.mRight;
					assert left != null && right != null;
					if (storePath.mStores != null) {
						final Set<Term> subInterpolants = new HashSet<Term>();

						// Rewrite "left" to "right" at shared indices to shorten the weq- or nweq-term
						Set<Term> sharedIndices = new HashSet<Term>();
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant;
							if (isAPath) {
								subInterpolant = mTheory.and(indexPath.mPathInterpolants[color]
										.toArray(new Term[indexPath.mPathInterpolants[color].size()]));
							} else {
								subInterpolant = mTheory.or(indexPath.mPathInterpolants[color]
										.toArray(new Term[indexPath.mPathInterpolants[color].size()]));
							}
							if (indexPath.mSharedIndex[color] != null && indexPath.mSharedIndex[color] != mDoubleDot) {
								sharedIndices.add(indexPath.mSharedIndex[color]);
								mPathInterpolants[color].add(subInterpolant);
							} else {
								subInterpolants.add(subInterpolant);
							}
						}
						final int order =
								storePath.mStores == null ? 0 : storePath.mStores.size() - sharedIndices.size();
						Term rewriteLeftAtShared = left;
						for (final Term idx : sharedIndices) {
							rewriteLeftAtShared =
									mTheory.term("store", rewriteLeftAtShared, idx, buildSelect(right, idx));
						}
						final Term formula;
						final Term interpolantClause;
						if (isAPath) { // The interpolant is a weq term including the sub-interpolants of local index
										// terms
							formula = mTheory.or(subInterpolants.toArray(new Term[subInterpolants.size()]));
							interpolantClause = buildWeqTerm(rewriteLeftAtShared, right, order, formula, mDoubleDot);
						} else { // The interpolant is an nweq term including the sub-interpolants of local index terms
							formula = mTheory.and(subInterpolants.toArray(new Term[subInterpolants.size()]));
							interpolantClause = buildNweqTerm(rewriteLeftAtShared, right, order, formula, mDoubleDot);
						}
						mPathInterpolants[color].add(interpolantClause);
					} else {
						Term interpolantClause = mTheory.equals(left, right);
						if (!isAPath) {
							interpolantClause = mTheory.not(interpolantClause);
						}
						mPathInterpolants[color].add(interpolantClause);
					}
				} else {
					if (storePath.mStores != null) {
						for (final Term index : storePath.mStores) {
							final WeakPathInfo indexPath = mIndexPathInfos.get(index);
							final Term subInterpolant;
							if (isAPath) {
								subInterpolant = mTheory.or(indexPath.mPathInterpolants[color]
										.toArray(new Term[indexPath.mPathInterpolants[color].size()]));
							} else {
								subInterpolant = mTheory.and(indexPath.mPathInterpolants[color]
										.toArray(new Term[indexPath.mPathInterpolants[color].size()]));
							}
							mPathInterpolants[color].add(subInterpolant);
						}
					}
				}
			}

			/**
			 * Build the recursive interpolant for mixed weakeq-ext (case 5.3).
			 * 
			 * The goal is to recursively build a shared term for the local array at the path end, using the shared
			 * array on the other path end, by storing for each index the correct value which we can find in the
			 * corresponding index path. Then, this shared array can be used in the "usual" extensionality interpolant.
			 * 
			 * @param color
			 *            The current partition
			 * @param other
			 *            The other path end
			 * @param recursionPath
			 *            The path on which we rewrite the shared array to the outer path end.
			 */
			private void buildRecursiveInterpolant(final int color, final WeakPathEnd other,
					final StorePath recursionPath) {
				final boolean isAPath = recursionPath.mIsAPath;

				// Build the innermost interpolant term "mixedVar=recursionVar /\ B-interpolant" if recursionPath is A
				// local, or "mixedVar!=recursionVar \/ A-interpolant" if recursionPath is B local
				final Term eqTerm = mTheory.equals(mDiseqInfo.getMixedVar(), mRecursionVar);
				// Compute A- or B-interpolant of the lemma where the store path is shortened by removing recursionPath.
				final Term innerInterpolant;
				if (isAPath) {
					innerInterpolant =
							mTheory.and(mPathInterpolants[color].toArray(new Term[mPathInterpolants[color].size()]));
				} else {
					innerInterpolant =
							mTheory.or(mPathInterpolants[color].toArray(new Term[mPathInterpolants[color].size()]));
				}
				mPathInterpolants[color].clear();
				Term recursiveInterpolant;
				if (isAPath) {
					recursiveInterpolant = mTheory.and(eqTerm, innerInterpolant);
				} else {
					recursiveInterpolant = mTheory.or(eqTerm, innerInterpolant);
				}

				// Recursion over the store indices on this outer path. On each index, the shared array is rewritten
				// towards the local array at the outer path end, to express the local array in shared terms.
				TermVariable lastRecVar = mRecursionVar;
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
							// Compute the "dual" interpolant
							BitSet oldInA = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = oldInA;
							indexPath.interpolateWeakPathInfo(false); // Compute the "dual" itp for the inner path only
							// Change back
							oldInA = mABSwitchOccur.mInB;
							mABSwitchOccur.mInB = mABSwitchOccur.mInA;
							mABSwitchOccur.mInA = oldInA;
							recPathInterpolantTerms = indexPath.mPathInterpolants[color];
						}

						if (indexPath.mSharedIndex[color] != null) { // Case 5.3 (i)
							rewriteAtIndex = indexPath.mSharedIndex[color];
							if (isAPath) {
								pathInterpolant = mTheory
										.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							} else {
								pathInterpolant = mTheory
										.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							}
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
								rewriteWithElement = buildSelect(rewriteToArray, rewriteAtIndex);
							}
						} else { // Case 5.3 (ii)
							final TermVariable cdot = mTheory.createFreshTermVariable("cdot", index.getSort());
							rewriteAtIndex = cdot;
							if (isAPath) {
								pathInterpolant = mTheory
										.or(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							} else {
								pathInterpolant = mTheory
										.and(recPathInterpolantTerms.toArray(new Term[recPathInterpolantTerms.size()]));
							}
							final Term lastSharedOnIndexPath = this.equals(mHead) ? indexPath.mTail.mLastChange[color]
									: indexPath.mHead.mLastChange[color];
							assert !(lastSharedOnIndexPath instanceof AnnotatedTerm
									&& mEqualities.containsValue(lastSharedOnIndexPath));
							rewriteToArray = lastSharedOnIndexPath;
							rewriteWithElement = buildSelect(rewriteToArray, rewriteAtIndex);
						}

						// Build the FPi Term for the outer path of the index path on the opposite side, i.e. for
						// the outer B path, if recursionPath is an A path, and for the outer A path otherwise.
						final Term fPi;
						// Needed for case without shared index (then there are no indexEqs)
						final int fPiOrderForRecursion;
						if (this.equals(mHead)) { // recursionPath is the left outer path
							final ArrayList<AnnotatedTerm> indexDiseqs = indexPath.mTail.mIndexDiseqs[color];
							fPiOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPi = indexPath.buildFPiTerm(!isAPath, color, rewriteAtIndex, indexDiseqs,
									indexPath.mTail.mIndexEqs[color]);
						} else { // recursionPath is the right outer path
							final ArrayList<AnnotatedTerm> indexDiseqs = indexPath.mHead.mIndexDiseqs[color];
							fPiOrderForRecursion = indexDiseqs == null ? 0 : indexDiseqs.size();
							fPi = indexPath.buildFPiTerm(!isAPath, color, rewriteAtIndex, indexDiseqs,
									indexPath.mHead.mIndexEqs[color]);
						}

						// Insert the rewritten term into the inner interpolant term
						final Term rewriteRecVar =
								mTheory.term("store", currentRecVar, rewriteAtIndex, rewriteWithElement);
						final Term rewriteRecInterpolant;
						if (isAPath) {
							rewriteRecInterpolant =
									mTheory.and(mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant), fPi);
						} else {
							rewriteRecInterpolant =
									mTheory.or(mTheory.let(lastRecVar, rewriteRecVar, recursiveInterpolant), fPi);
						}

						// Build the final recursive interpolant
						if (indexPath.mSharedIndex[color] != null) { // Case 5.3 (i): use shared index to rewrite
							if (isAPath) {
								recursiveInterpolant = mTheory.or(pathInterpolant, rewriteRecInterpolant);
							} else {
								recursiveInterpolant = mTheory.and(pathInterpolant, rewriteRecInterpolant);
							}
						} else { // Use nweq (if recursionPath is A local) or weq to express rewrite index (5.3(ii))
							assert rewriteAtIndex instanceof TermVariable;
							assert rewriteToArray != null;
							final TermVariable rewriteDot = (TermVariable) rewriteAtIndex;
							final Set<Term> rewriteIndexFinders = new HashSet<Term>();
							// If resursionPath is A-local, build the nweq terms for all inner paths of the main store
							// path; otherwise the weq terms. They are used to express the rewrite index.
							for (final StorePath path : mStorePaths[color]) {
								final Term left = path.mLeft;
								final Term right = path.mRight;
								if (left != null && right != null) {
									final int order = path.mStores != null ? path.mStores.size() : 0;
									final Term rewriteIndexSearcher;
									if (isAPath) {
										rewriteIndexSearcher =
												buildNweqTerm(left, right, order, rewriteRecInterpolant, rewriteDot);
									} else {
										rewriteIndexSearcher =
												buildWeqTerm(left, right, order, rewriteRecInterpolant, rewriteDot);
									}
									rewriteIndexFinders.add(rewriteIndexSearcher);
								}
							}
							// Build the nweq term for the concatenation of the outer B-paths on store and index path,
							// if recursionPath is A-local, and a weq term for the outer A-paths else. It is used to
							// express the rewrite index.
							final Term concatLeft = other.mLastChange[color];
							final Term concatRight = rewriteToArray;
							final Set<Term> otherMainStores = other.mMainStores[color];
							final int concatStores =
									fPiOrderForRecursion + (otherMainStores == null ? 0 : otherMainStores.size());
							final Term concatTerm;
							if (isAPath) {
								concatTerm = buildNweqTerm(concatLeft, concatRight, concatStores, rewriteRecInterpolant,
										rewriteDot);
							} else {
								concatTerm = buildWeqTerm(concatLeft, concatRight, concatStores, rewriteRecInterpolant,
										rewriteDot);
							}
							rewriteIndexFinders.add(concatTerm);
							final Term recursionStepTerm;
							if (isAPath) {
								recursionStepTerm =
										mTheory.or(rewriteIndexFinders.toArray(new Term[rewriteIndexFinders.size()]));
							} else {
								recursionStepTerm =
										mTheory.and(rewriteIndexFinders.toArray(new Term[rewriteIndexFinders.size()]));
							}
							recursiveInterpolant = mTheory.let(lastRecVar, currentRecVar, recursiveInterpolant);
							if (isAPath) {
								recursiveInterpolant =
										mTheory.or(recursiveInterpolant, pathInterpolant, recursionStepTerm);
							} else {
								recursiveInterpolant =
										mTheory.and(recursiveInterpolant, pathInterpolant, recursionStepTerm);
							}
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
	 * Helper class to store the information from the store path in weakeq-ext.
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
