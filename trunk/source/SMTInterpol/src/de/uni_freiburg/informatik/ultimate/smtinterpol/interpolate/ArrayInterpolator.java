/*
 * Copyright (C) 2016 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseTermInfo.ProofPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the theory of arrays. At the moment, it can deal with read-over-weakeq lemmas only;
 * extensionality is not yet supported.
 * 
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class ArrayInterpolator {
	
	// General info to set up the ArrayInterpolator
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	/**
	 * The conjuncts and disjuncts that build the interpolants, mapped to "and"/"or" to remember how to connect them.
	 */
	private final Map<Term, String>[] mInterpolants;
	
	// Information for array lemmas
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
	
	// Specific information for read-over-weakeq-lemmas
	/**
	 * The strong path between the select indices of the main disequality.
	 */
	private ApplicationTerm mIndexEquality;
	/**
	 * The store path between the arrays of the main disequality for equivalence modulo i, where i is the path index.
	 */
	private ProofPath mStorePath;
	/**
	 * This contains the shared select index for all partitions where it exists.
	 */
	private Term[] mSelectIndex;
	
	@SuppressWarnings("unchecked")
	public ArrayInterpolator(Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
		mInterpolants = new Map[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashMap<Term, String>();
		}
	}
	
	/**
	 * Compute interpolants for array lemmas. At the moment, this covers only read-over-weakeq lemmas.
	 * 
	 * @param proofTerm
	 *            The lemma that is interpolated
	 * @return An array containing interpolants for the different partitions
	 */
	public Term[] computeInterpolants(Term proofTerm) {
		mLemmaInfo = mInterpolator.getClauseTermInfo(proofTerm);
		
		// At the moment, we only support read-over-weakeq lemmas
		assert mLemmaInfo.getLemmaType().equals(":read-over-weakeq");
		
		mDiseq = (ApplicationTerm) mLemmaInfo.getDiseq();
		mDiseqInfo = mInterpolator.getLiteralInfo(mDiseq);
		mEqualities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		mDisequalities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
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
		interpolants = computeReadOverWeakeqInterpolants(proofTerm);
		return interpolants;
	}
	
	/**
	 * Compute interpolants for a read-over-weakeq lemma. The lemma consists of a disequality of form "a[i] != b[j]", a
	 * (strong) path of length 2 for the index equality "i = j" unless the disequality is of form "a[i] != b[i]", and a
	 * weak path from array "a" to array "b" consisting of equality or store steps with store operations only at indices
	 * different from the weakpath index, which is one of the select indices. There are basically three cases for
	 * interpolation: either (i) there is a shared index term -> terms of the form "s1[x]=s2[x]" or "s1[x]!=s2[x]" are
	 * built; or the index equality is (ii) A-local -> terms of the form "nweq(s1,s2,k,F(·))" are built for B paths; or
	 * the index equality is (iii) B-local -> terms of the form "weq(s1,s2,k,F(·))" are built for A paths.
	 * 
	 * @param proofTerm
	 *            The lemma which interpolants are calculated for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeReadOverWeakeqInterpolants(Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length <= 2;
		if (paths.length == 2) {
			final Term[] indexPath = paths[0].getIndex() == null ? paths[0].getPath() : paths[1].getPath();
			assert indexPath.length == 2;
			mIndexEquality = mEqualities.get(new SymmetricPair<Term>(indexPath[0], indexPath[1]));
			mStorePath = indexPath == paths[0].getPath() ? paths[1] : paths[0];
		} else { // In this case, the main disequality is of form "a[i] != b[i]"
			assert paths.length == 1;
			mStorePath = paths[0];
		}
		WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);
		
		// Determine the shared select index for all partitions where it exists
		calculateSharedSelectIndices();
		// Calculate the interpolant terms from the store path
		arrayPath.interpolatePathInfoReadOverWeakeq();
		// In some cases, the index equality has to be added
		if (mIndexEquality != null) {
			addIndexEquality();
		}
		
		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			Set<Term> disjuncts = new HashSet<Term>();
			Set<Term> conjuncts = new HashSet<Term>();
			for (Term term : mInterpolants[color].keySet()) {
				if (mInterpolants[color].get(term).equals("and")) {
					conjuncts.add(term);
				} else {
					assert mInterpolants[color].get(term).equals("or");
					disjuncts.add(term);
				}
			}
			if (!disjuncts.isEmpty()) {
				conjuncts.add(mTheory.or(disjuncts.toArray(new Term[disjuncts.size()])));
			}
			interpolants[color] = mTheory.and(conjuncts.toArray(new Term[conjuncts.size()]));
		}
		return interpolants;
	}
	
	/**
	 * Determine for all partitions whether there exists a shared select index. This can be the weakpathindex, if no
	 * index equality exists; the mixed variable, if the index equality is mixed; the weakpathindex, if the index
	 * equality is local or shared; the other select index, if the index equality is A- or B-local, and weakpathindex is
	 * not shared. Note: if both select indices are shared, take weakpathindex. This information is used during
	 * interpolation to determine the partitions where a "simple" interpolant can be built.
	 */
	private void calculateSharedSelectIndices() {
		mSelectIndex = new Term[mNumInterpolants];
		// If the main disequality is of form "a[i] != b[i]", there is no path for the index equality
		if (mIndexEquality == null) {
			// Check if the weakpath index is shared
			Term index = mStorePath.getIndex();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mInterpolator.getOccurrence(index, null).isAB(color)) {
					mSelectIndex[color] = index;
				}
			}
		} else {
			for (int color = 0; color < mNumInterpolants; color++) {
				// Check if the weakpath index is shared
				if (mInterpolator.getOccurrence(mStorePath.getIndex(), null).isAB(color)) {
					mSelectIndex[color] = mStorePath.getIndex();
				} else {
					LitInfo info = mInterpolator.getLiteralInfo(mIndexEquality);
					// Check if there is a mixed variable
					if (info.isMixed(color)) {
						mSelectIndex[color] = info.getMixedVar();
					} else { // Check the other select index
						assert info.isALocal(color) || info.isBLocal(color);
						Term index = ((ApplicationTerm) mIndexEquality).getParameters()[0];
						index = index == mStorePath.getIndex() ? ((ApplicationTerm) mIndexEquality).getParameters()[1]
								: index;
						if (mInterpolator.getOccurrence(index, null).isAB(color)) {
							mSelectIndex[color] = index;
						}
					}
				}
			}
		}
	}
	
	/**
	 * For read-over-weakeq, the index equality has to be included in the interpolant if both indices are shared and
	 * either a) it is A-local and the main diseq is mixed or B -> it is added as conjunct to the interpolant, or b) it
	 * is B-local and the main diseq is A -> it is a premise for the path summaries
	 */
	private void addIndexEquality() {
		final LitInfo info = mInterpolator.getLiteralInfo(mIndexEquality);
		final Term otherSelect = info.getMixedVar() != null ? info.getMixedVar()
				: getIndexFromSelect((ApplicationTerm) mDiseq.getParameters()[0]).equals(mStorePath.getIndex())
						? mDiseq.getParameters()[1] : mDiseq.getParameters()[0];
		final Occurrence otherSelectOccur = mInterpolator.getOccurrence(otherSelect, null);
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mSelectIndex[color] != null) {
				if (mDiseqInfo.isALocal(color)) {
					if (info.isBLocal(color)) {
						mInterpolants[color].put(mTheory.not(mIndexEquality), "or");
					}
				} else {
					if (info.isALocal(color) && otherSelectOccur.isBorShared(color)) {
						mInterpolants[color].put(mIndexEquality, "and");
					}
				}
			}
		}
	}
	
	/**
	 * Compute the parent partition. This is the next partition whose subtree includes color.
	 */
	private int getParent(int color) {
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
	private int getChild(int color, Occurrence occur) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
	
	// Methods to deal with array terms
	private static boolean isSelectTerm(Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("select");
		}
		return false;
	}
	
	private static boolean isStoreTerm(Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("store");
		}
		return false;
	}
	
	private static Term getArrayFromSelect(ApplicationTerm select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[0];
	}
	
	private static Term getIndexFromSelect(ApplicationTerm select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[1];
	}
	
	private static Term getArrayFromStore(ApplicationTerm store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[0];
	}
	
	private static Term getIndexFromStore(ApplicationTerm store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[1];
	}
	
	/**
	 * Build a select equality to summarize an inner A-path in the simple case for read-over-weakeq.
	 * 
	 * @param pre
	 *            the premise for the select equality to hold (negated, to add it as disjunct).
	 * @param left
	 *            the shared array at the left path end.
	 * @param right
	 *            the shared array at the right path end.
	 * @param index
	 *            the shared index for which the arrays match, i.e. the shared term for the weakpath index.
	 * @return an interpolant term of the form "¬pre \/ left[index]=right[index]"
	 */
	private Term buildSelectEqTerm(Set<Term> pre, Term left, Term right, Term index) {
		final Term prePart = pre == null ? mTheory.mFalse : mTheory.or(pre.toArray(new Term[pre.size()]));
		final Term leftSelect = mTheory.term("select", left, index);
		final Term rightSelect = mTheory.term("select", right, index);
		final Term selectEq = mTheory.equals(leftSelect, rightSelect);
		return mTheory.or(prePart, selectEq);
	}
	
	/**
	 * Build a weq term for two arrays and a given formula. It states that two arrays differ at most at #stores
	 * positions, and each difference satisfies F.
	 * 
	 * @param color
	 *            the current partition
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
	private Term buildWeqTerm(Term left, Term right, int order, Term formula, TermVariable auxVar) {
		Term rewrite = left;
		Term weqTerm = mTheory.mTrue;
		
		for (int m = 0; m < order; m++) {
			Term arrayEquality = mTheory.equals(rewrite, right);
			Term diffTerm = mTheory.term("@diff", rewrite, right);
			Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			weqTerm = mTheory.and(weqTerm, mTheory.or(arrayEquality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		weqTerm = mTheory.and(weqTerm, mTheory.equals(rewrite, right));
		
		return weqTerm;
	}
	
	/**
	 * Build an nweq term for two arrays and a given formula. It states that two arrays differ at some index that
	 * satisfies F or on more than #stores indices.
	 * 
	 * @param color
	 *            the current partition
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
	private Term buildNweqTerm(Term left, Term right, int order, Term formula, TermVariable auxVar) {
		Term rewrite = left;
		Term weqTerm = mTheory.mFalse;
		
		for (int m = 0; m < order; m++) {
			Term arrayDisequality = mTheory.not(mTheory.equals(rewrite, right));
			Term diffTerm = mTheory.term("@diff", rewrite, right);
			Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			weqTerm = mTheory.or(weqTerm, mTheory.and(arrayDisequality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		weqTerm = mTheory.or(weqTerm, mTheory.not(mTheory.equals(rewrite, right)));
		
		return weqTerm;
	}
	
	/**
	 * Build the F_pi^A - term. It collects the B-parts of index disequalities on an A-path.
	 * 
	 * @param color
	 *            the current partition
	 * @param sharedIndex
	 *            the shared term representing the weakpathindex
	 * @param indexDiseqs
	 *            disequalities between weakpathindex and all indices for which a store between left and right exists.
	 * @return the disjunction of the negated B-parts of index diseqs on an A-path, in shared terms.
	 */
	private Term buildFPiATerm(int color, TermVariable sharedIndex, Map<ApplicationTerm, LitInfo> indexDiseqs) {
		if (indexDiseqs == null) {
			return mTheory.mFalse;
		}
		Set<Term> indexTerms = new HashSet<Term>();
		for (ApplicationTerm diseq : indexDiseqs.keySet()) {
			final LitInfo info = indexDiseqs.get(diseq);
			// Index diseqs are either mixed or B-local.
			// In the first case, there is a mixed term, in the second, the store index is shared.
			final Term index = info.isMixed(color) ? info.getMixedVar()
					: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
							: diseq.getParameters()[0];
			indexTerms.add(mTheory.equals(index, sharedIndex));
		}
		Term fATerm = mTheory.or(indexTerms.toArray(new Term[indexTerms.size()]));
		return fATerm;
	}
	
	/**
	 * Build the F_pi^B - term. It collects the A-parts of index disequalities on a B-path.
	 * 
	 * @param color
	 *            the current partition
	 * @param sharedIndex
	 *            the shared term representing the weakpathindex
	 * @param indexDiseqs
	 *            disequalities between weakpathindex and all indices for which a store between left and right exists.
	 * @return the conjunction of the A-parts of index diseqs on a B-path, in shared terms.
	 */
	private Term buildFPiBTerm(int color, TermVariable sharedIndex, Map<ApplicationTerm, LitInfo> indexDiseqs) {
		if (indexDiseqs == null) {
			return mTheory.mTrue;
		}
		Set<Term> indexTerms = new HashSet<Term>();
		for (ApplicationTerm diseq : indexDiseqs.keySet()) {
			final LitInfo info = indexDiseqs.get(diseq);
			// Index diseqs are either mixed or A-local.
			// In the first case, there is a mixed term, in the second, the store index is shared.
			final Term index = info.isMixed(color) ? info.getMixedVar()
					: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
							: diseq.getParameters()[0];
			if (info.isMixed(color)) { // Add the A projection of the index disequality (an equality in the mixed case)
				indexTerms.add(mTheory.equals(index, sharedIndex));
			} else if (info.isALocal(color)) {
				// If the index diseq is A local, the A projection is the diseq itself.
				indexTerms.add(mTheory.not(mTheory.equals(index, sharedIndex)));
			}
		}
		Term fBTerm = mTheory.and(indexTerms.toArray(new Term[indexTerms.size()]));
		return fBTerm;
	}
	
	class WeakPathInfo {
		Term mPathIndex;
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
		
		boolean mComputed;
		
		public WeakPathInfo(ProofPath path) {
			mPathIndex = path.getIndex();
			mPath = path.getPath();
			mHasABPath = new BitSet(mNumInterpolants);
			mHasABPath.set(0, mNumInterpolants);
			mMaxColor = mNumInterpolants;
		}
		
		/**
		 * Calculate the interpolants for the complete weakpath and all partitions for read-over-weakeq.
		 */
		public void interpolatePathInfoReadOverWeakeq() {
			if (mComputed) {
				return;
			}
			
			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();
			
			final Term[] mainSelects = mDiseq.getParameters();
			
			// Determine whether to start with A or B or AB and open A paths accordingly.
			final Term headSelect = getArrayFromSelect((ApplicationTerm) mainSelects[0]).equals(mPath[0])
					? mainSelects[0] : mainSelects[1];
			final Occurrence headOccur = mInterpolator.getOccurrence(headSelect, null);
			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);
			
			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm;
				boundaryTerm = mPath[i];
				
				// Each step in a weak path can be either an equality literal or a store step of form "a (store a i v)".
				// In the second case, there is no literal in the lemma.
				if (lit == null) {
					// A store step can only open or close a path at term "a" if "a" is the left term;
					// we also open (resp. close) at shared stores if the index diseq "storeindex != weakpathindex" is
					// A-local (resp. B-local) to avoid collecting the diseq.
					// after this, we store the index disequality "storeindex != weakpathindex" for the interpolant if
					// it is mixed, or if it is A-local on a B-local path or vice versa.
					final Term storeTerm =
							isStoreTerm(left) && getArrayFromStore((ApplicationTerm) left).equals(right) ? left : right;
					final Term arrayTerm = storeTerm.equals(left) ? right : left;
					assert getArrayFromStore((ApplicationTerm) storeTerm).equals(arrayTerm);
					Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm, null);
					final Term storeIndex = getIndexFromStore((ApplicationTerm) storeTerm);
					ApplicationTerm indexDiseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
					Occurrence indexDiseqOcc = mInterpolator.getLiteralInfo(indexDiseq);
					Occurrence intersectOcc = stepOcc.intersect(indexDiseqOcc);
					
					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.closeAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addIndexDisequality(mHead, storeTerm);
				} else { // In equality steps, we just close or open A paths.
					LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (((LitInfo) stepInfo).getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(mPath[i + 1], null);
						boundaryTerm = ((LitInfo) stepInfo).getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}
			
			// Determine whether the path can be closed at mPath[mPath.length-1].
			// This is the case when tailSelect is in A (resp. B) while we are currently in B (resp. A).
			final Term tailSelect = headSelect.equals(mainSelects[0]) ? mainSelects[1] : mainSelects[0];
			final Occurrence tailOccur = mInterpolator.getOccurrence(tailSelect, null);
			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);
			
			// Paths which are still open at mPath[0] or mPath[mPath.length - 1] have to be closed using the main diseq.
			// Note that we might need mixed vars in the case where we build select equalities.
			closeReadOverWeakeq();
			
			mComputed = true;
		}
		
		/**
		 * Close the outer paths which are still open at the left or right end. There is nothing to do in the cases
		 * where we don't have a shared index, because if there was an A local outer path in the B-local case (or vice
		 * versa), it has already been closed by using either head- or tailOccur. For partitions where the main diseq is
		 * mixed, we have to close all the partitions on the way from mHead.mColor to mTail.mColor (except for their lca
		 * partition). For partitions where the main diseq is A(resp. B)-local or shared and a shared select index
		 * exists, B(resp. A)-local and mixed index diseqs on outer A(resp. B)-paths have to be added to the interpolant
		 * as premise (resp. conjunct).
		 */
		private void closeReadOverWeakeq() {
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
					break;
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
				if (mSelectIndex[color] == null) { // Nothing to do in the cases where no shared select index exists.
					continue;
				}
				if (mHead.mIndexDiseqs[color] == null && mTail.mIndexDiseqs[color] == null) { // No index diseqs to add.
					continue;
				}
				final Term index = mSelectIndex[color];
				Map<ApplicationTerm, LitInfo> allDiseqs = new HashMap<ApplicationTerm, LitInfo>();
				if (mHead.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mHead.mIndexDiseqs[color]);
				}
				if (mTail.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mTail.mIndexDiseqs[color]);
				}
				if (mDiseqInfo.isALocal(color)) {
					// A-local outer paths must be closed, B-local ones are already apart from the shared case.
					assert mHead.mTerm[color] != null || mTail.mTerm[color] != null; // one of the outer paths is in A
					// Add the B part of the diseqs as premise for the interpolant
					for (ApplicationTerm diseq : allDiseqs.keySet()) {
						LitInfo diseqInfo = allDiseqs.get(diseq);
						// get the other shared index, this is either the mixed var or the store index
						final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
								: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
										: diseq.getParameters()[0];
						mInterpolants[color].put(mTheory.equals(index, otherIndex), "or");
					}
					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
				} else {
					assert mDiseqInfo.isBLocal(color);
					// B-local paths must be closed, A-local ones are already, at the latest in the 1st part.
					assert mHead.mTerm[color] == null || mTail.mTerm[color] == null; // one of the outer paths is in B
					// Add the A part of the diseqs as conjunct to the interpolant
					for (ApplicationTerm diseq : allDiseqs.keySet()) {
						LitInfo diseqInfo = allDiseqs.get(diseq);
						final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
								: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
										: diseq.getParameters()[0];
						// If the diseq is mixed, the A-projection is a positive EQ-term
						Term diseqInSharedTerms = mTheory.equals(index, otherIndex);
						// else, it is a disequality literal.
						if (!diseqInfo.isMixed(color)) {
							diseqInSharedTerms = mTheory.not(diseqInSharedTerms);
						}
						mInterpolants[color].put(diseqInSharedTerms, "and");
					}
					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
				}
			}
		}
		
		class WeakPathEnd {
			/**
			 * The first partition for which there is an A-local prefix of the path. If mHasABPath is non-empty, this is
			 * the first partition that is not in mHasABPath, i.e. the first for which only a continuous A-path but not
			 * a continuous B-path exists.
			 */
			int mColor;
			/**
			 * For each partition this gives the term that ends the first A-local chain of equalities. Note that
			 * mTerm[color] is distinct from null only for paths which are still open on the opposite end.
			 */
			Term[] mTerm;
			/**
			 * For each partition, this gives the term which marks the last change from A to B or vice versa. This can
			 * be the same term as in mTerm if the path is A local and still open on the opposite side.
			 */
			Term[] mLastChange;
			/**
			 * For each partition this gives the set of B(resp. A)-local and mixed store index disequalities found on
			 * the A (resp. B) path so far.
			 */
			Map<ApplicationTerm, LitInfo>[] mIndexDiseqs;
			
			@SuppressWarnings("unchecked")
			public WeakPathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
				mLastChange = new Term[mNumInterpolants];
				mIndexDiseqs = new Map[mNumInterpolants];
			}
			
			public void closeAPath(WeakPathEnd other, Term boundary, Occurrence occur) {
				assert (other.mColor <= mMaxColor);
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					closeSingleAPath(other, boundary);
				}
			}
			
			public void openAPath(WeakPathEnd other, Term boundary, Occurrence occur) {
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
			private void closeSingleAPath(WeakPathEnd other, Term boundary) {
				// This should be empty now, since we anded it with occur.mInA and the occurrence is not in A for color.
				assert mHasABPath.isEmpty();
				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) { // the path is already closed at the left side
					// Add the interpolant clause for this A path.
					addInterpolantClauseAPath(color, boundary);
					mTerm[color] = null;
				} else {
					assert (mMaxColor == color);
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
			private void openSingleAPath(WeakPathEnd other, Term boundary, int child) {
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
					addInterpolantClauseBPath(mColor, boundary);
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
			 * @param storeOccur
			 *            The occurrence of the store term.
			 */
			private void addIndexDisequality(WeakPathEnd other, Term storeTerm) {
				assert isStoreTerm(storeTerm);
				final Term storeIndex = getIndexFromStore((ApplicationTerm) storeTerm);
				ApplicationTerm diseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
				LitInfo diseqInfo = mInterpolator.getLiteralInfo(diseq);
				
				// The diseq has to be added to all partitions where it is mixed and all partitions that lie on the
				// tree path between the partition of the diseq and the partition of the store term.
				// In nodes under the lca which are not on the way, both are in B, in nodes above the lca both are in A,
				// and in both cases there is nothing to do.
				addIndexDiseqColors(other, diseqInfo, diseq, diseqInfo);
				if (diseqInfo.getMixedVar() != null) {
					// additionally go up and down with weakpathindexoccur
					final Occurrence occur = mInterpolator.getOccurrence(mStorePath.getIndex(), null);
					addIndexDiseqColors(other, occur, diseq, diseqInfo);
				}
			}
			
			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index disequality to
			 * those partitions. This adds the index disequality to all partitions where it is not in A (resp. B) while
			 * the path is.
			 */
			private void addIndexDiseqColors(WeakPathEnd other, Occurrence occur, ApplicationTerm diseq,
					LitInfo diseqInfo) {
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
			private void addIndexDiseqOneColor(WeakPathEnd other, ApplicationTerm diseq, LitInfo diseqInfo, int color) {
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
			 * Add an interpolant clause for a closed A path. Case 1 (shared select index): a) (mDiseq A-local): B-local
			 * index diseqs are a premise for all interpolant parts summarizing A paths. b) (else): the conjunction of
			 * all B-local or the B-part of mixed index diseqs on this path is a premise for the arrays at the path ends
			 * to coincide at weakpathindex => interpolant of the form "i!=k1/\.../\i!=kn->start[i]=end[i]". Case 2
			 * (A-local, no shared select index): Nothing to do. Case 3 (B-local, no shared select index): Summarize the
			 * path by a WEQ term stating that the arrays at the path end differ at most at k locations (k= # of B-local
			 * and mixed index diseqs on the path) which are all different from weakpathindex.
			 */
			private void addInterpolantClauseAPath(int color, Term boundary) {
				Term left = mLastChange[color];
				Term right = boundary;
				if (mSelectIndex[color] != null) { // Case 1
					if (mDiseqInfo.isALocal(color)) { // Case 1a
						if (mIndexDiseqs[color] != null) {
							for (ApplicationTerm diseq : mIndexDiseqs[color].keySet()) {
								// both indices must be shared in this case
								assert mInterpolator.getOccurrence(diseq.getParameters()[0], null).isAB(color);
								assert mInterpolator.getOccurrence(diseq.getParameters()[1], null).isAB(color);
								mInterpolants[color].put(diseq, "or");
							}
							mIndexDiseqs[color] = null;
						}
					} else { // Case 1b
						Term index = mSelectIndex[color];
						Set<Term> pre = new HashSet<Term>();
						if (mIndexDiseqs[color] != null) {
							
							for (ApplicationTerm diseq : mIndexDiseqs[color].keySet()) {
								LitInfo diseqInfo = mIndexDiseqs[color].get(diseq);
								// get the other shared index, this is either the mixed variable or the store index
								final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
										: diseq.getParameters()[0].equals(mStorePath.getIndex())
												? diseq.getParameters()[1] : diseq.getParameters()[0];
								pre.add(mTheory.equals(index, otherIndex));
							}
							mIndexDiseqs[color] = null;
						}
						Term itpClause = buildSelectEqTerm(pre, left, right, index);
						mInterpolants[color].put(itpClause, "and");
					}
				} else if (mDiseqInfo.isALocal(color)) { // Case 2
					mIndexDiseqs[color] = null; // should be null before
					return;
				} else {
					assert mDiseqInfo.isBLocal(color);
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					Term fPiA = buildFPiATerm(color, cdot, mIndexDiseqs[color]);
					Term itpClause = buildWeqTerm(left, right, order, fPiA, cdot);
					mInterpolants[color].put(itpClause, "and");
					mIndexDiseqs[color] = null;
				}
			}
			
			/**
			 * Add an interpolant clause for a closed B path. Case 1 (shared select index): A-local and the A part of
			 * mixed index disequalities are added as conjunct to the entire lemma interpolant. a) Additionally, for
			 * mDiseq A-local: Summarize the path by stating that the arrays at the path ends differ at weakpathindex =>
			 * interpolant conjunct of the form "start[i] != end[i]". Case 2 (A-local, no shared select index):
			 * Summarize the path by an NWEQ term stating that the arrays at the path end differ at least at k locations
			 * (k= # B-local and mixed index diseqs on the path) of which (at least) one equals the weakpathindex. Case
			 * 3 (B-local, no shared select index): Nothing to do.
			 */
			private void addInterpolantClauseBPath(int color, Term boundary) {
				Term left = mLastChange[color];
				Term right = boundary;
				if (mSelectIndex[color] != null) { // Case 1
					Term index = mSelectIndex[color];
					if (mIndexDiseqs[color] != null) {
						for (ApplicationTerm diseq : mIndexDiseqs[color].keySet()) {
							LitInfo diseqInfo = mIndexDiseqs[color].get(diseq);
							final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
									: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
											: diseq.getParameters()[0];
							// If the diseq is mixed, the A-projection is a positive EQ-term
							Term diseqInSharedTerms = mTheory.equals(index, otherIndex);
							// else, it is a disequality literal.
							if (!diseqInfo.isMixed(color)) {
								diseqInSharedTerms = mTheory.not(diseqInSharedTerms);
							}
							mInterpolants[color].put(diseqInSharedTerms, "and");
						}
					}
					if (mDiseqInfo.isALocal(color)) { // Case 1a
						Term itpClause = buildSelectEqTerm(null, left, right, index);
						itpClause = mTheory.not(itpClause);
						mInterpolants[color].put(itpClause, "or");
					}
					mIndexDiseqs[color] = null;
				} else if (mDiseqInfo.isALocal(color)) { // Case 2
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					Term fPiB = buildFPiBTerm(color, cdot, mIndexDiseqs[color]);
					Term itpClause = buildNweqTerm(left, right, order, fPiB, cdot);
					mInterpolants[color].put(itpClause, "or");
					mIndexDiseqs[color] = null;
				} else { // Case 3
					assert mDiseqInfo.isBLocal(color);
					mIndexDiseqs[color] = null; // should be null before
					return;
				}
			}
			
			/**
			 * Add an interpolant clause for an A path ending at the very left or very right path end. This is only used
			 * for partitions where the main disequality is mixed or shared. => interpolant conjunct of the form
			 * "i!=k1/\.../\i!=kn->start[i]=end[i]" Note that one needs the mixedVar here if mDiseqInfo.isMixed(color).
			 * 
			 * @param color
			 *            the current partition
			 */
			private void addInterpolantClauseOuterAPath(int color) {
				// Add the interpolant for the outer (A) path
				final Term index = mSelectIndex[color];
				assert index != null;
				final Term inner = mTheory.term("select", mLastChange[color], index);
				Term outer;
				if (mDiseqInfo.isMixed(color)) {
					outer = mDiseqInfo.getMixedVar();
				} else {
					if (this.equals(mHead)) { // we are on a left outer A path
						outer = mTheory.term("select", mPath[0], index);
					} else { // we are on a right outer A path
						outer = mTheory.term("select", mPath[mPath.length - 1], index);
					}
				}
				
				Set<Term> diseqsInSharedTerms = new HashSet<Term>();
				if (mIndexDiseqs[color] != null) {
					for (ApplicationTerm diseq : mIndexDiseqs[color].keySet()) {
						LitInfo diseqInfo = mIndexDiseqs[color].get(diseq);
						if (diseqInfo.isBLocal(color) || diseqInfo.isMixed(color)) {
							final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
									: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
											: diseq.getParameters()[0];
							diseqsInSharedTerms.add(mTheory.equals(index, otherIndex));
						}
					}
				}
				mIndexDiseqs[color] = null;
				
				/*
				 * Here, we have to add the index diseq if we are on a right outer A-path in the mixed case where the
				 * index equality is B-local and both indices are shared.
				 */
				Term indexEq = mTheory.mFalse;
				if (this.equals(mTail) && mDiseqInfo.isMixed(color)) {
					final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
					final Term otherIndex = indexEqInfo.getMixedVar() != null ? indexEqInfo.getMixedVar()
							: mIndexEquality.getParameters()[0].equals(mStorePath.getIndex())
									? mIndexEquality.getParameters()[1] : mIndexEquality.getParameters()[0];
					final Occurrence otherIndexOccur = mInterpolator.getOccurrence(otherIndex, null);
					if (indexEqInfo.isBLocal(color) && otherIndexOccur.isAB(color)) {
						indexEq = mTheory.not(mIndexEquality);
					}
				}
				
				final Term pre = mTheory.or(indexEq,
						mTheory.or(diseqsInSharedTerms.toArray(new Term[diseqsInSharedTerms.size()])));
				final Term itpClause = mTheory.or(pre, mTheory.equals(outer, inner));
				mInterpolants[color].put(itpClause, "and");
			}
			
			/**
			 * Add an interpolant clause for a B path ending at the very left or very right path end. This is only
			 * needed for partitions where mDiseq is mixed or shared.
			 * 
			 * @param color
			 *            the current partition
			 */
			private void addInterpolantClauseOuterBPath(int color) {
				final Term index = mSelectIndex[color];
				assert index != null;
				if (mIndexDiseqs[color] != null) {
					for (ApplicationTerm diseq : mIndexDiseqs[color].keySet()) {
						LitInfo diseqInfo = mIndexDiseqs[color].get(diseq);
						if (diseqInfo.isALocal(color) || diseqInfo.isMixed(color)) {
							final Term otherIndex = diseqInfo.getMixedVar() != null ? diseqInfo.getMixedVar()
									: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
											: diseq.getParameters()[0];
							// If the diseq is mixed, the A projection is a positive EQ-term
							Term diseqInSharedTerms = mTheory.equals(index, otherIndex);
							// else we have a disequality
							if (!diseqInfo.isMixed(color)) {
								diseqInSharedTerms = mTheory.not(diseqInSharedTerms);
							}
							mInterpolants[color].put(diseqInSharedTerms, "and");
						}
					}
				}
				mIndexDiseqs[color] = null;
			}
		}
	}
}
