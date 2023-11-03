/*
 * Copyright (C) 2009-2016 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for congruence-closure theory lemmata.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class CCInterpolator {

	Interpolator mInterpolator;
	LitInfo mDiseqOccurrences;
	HashMap<SymmetricPair<Term>, LitInfo> mEqualityOccurrences;

	Theory mTheory;
	int mNumInterpolants;
	Collection<Term>[] mInterpolants;

	Term[] mPath;

	/**
	 * As long as there is a partition where the whole path is shared, this is the set of partitions for which all
	 * literals seen so far are in A.
	 */
	BitSet mAllInA;

	/**
	 * The first partition for which the path from start to end is in A. As long as mAllInA is not empty, this is the
	 * parent of all partition for which the path is AB-shared, i.e. the first partition where some literal is A-local.
	 */
	int mMaxColor;
	PathEnd mHead, mTail;

	/*
	 * max color is the maximum of all firstColor of all literals on the path.
	 *
	 * Head color is the lastColor of the first literal before the first path change. If head color >= max color, then
	 * there is no path change.
	 *
	 */

	/*
	 * invariants: HeadTerm[p] != null exactly for p in [m_HeadColor, m_MaxColor-1] HeadPre[p] != null only for p in
	 * [m_HeadColor, numInterpolants] HeadColor is in between first and last color of head term. likewise for Tail.
	 * MaxColor is maximum of all first of all terms and literals involved in current path.
	 *
	 * The partial interpolant of the current path is m_Interpolants && HeadPre ==> Lits[0] == m_HeadTerm && TailPre ==>
	 * m_TailTerm == lits[n] where HeadTerm = Lits[0] for partitions < HeadColor and TailTerm = Lits[n] for partitions <
	 * TailColor.
	 *
	 * For partitions >= maxColor, everything so far was in A, so the partial interpolant of the current path is
	 * m_Interpolants && TailPre ==> Lits[0] == lits[n]
	 */

	class PathEnd {
		/**
		 * The first partition for which there is an A-local prefix of the path. If m_hasABPath is non-empty, this is
		 * the first partition that is not in m_hasABPath, i.e. the first for which only a continuous A-path but not a
		 * continuous B-path exists.
		 */
		int mColor;
		/**
		 * For each partition on the path from m_Color to m_MaxColor this gives the term that ends the first A-local
		 * chain of equalities.
		 */
		Term[] mTerm;

		public PathEnd() {
			mColor = mNumInterpolants;
			mTerm = new Term[mNumInterpolants];
		}

		/**
		 * Closes all A paths and goes up the tree until the occurrence is in A or mixed.
		 *
		 * @param other
		 *            the other path end, usually head.
		 * @param boundaryTerm
		 *            the boundary term
		 * @param occur
		 *            the occurrence of the term/literal that we use
		 */
		public void closeAPath(final PathEnd other, final Term boundaryTerm, final Occurrence occur) {
			assert (other.mColor <= mMaxColor);
			mAllInA.and(occur.mInA);
			while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
				// No partition contains the whole path, because at least one literal was A-local in mColor and
				// this literal is B-local
				mAllInA.clear();

				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) {
					// we have an open A-path, which we close by adding the equality to the interpolant.
					mInterpolants[color].add(mTheory.term("=", mTerm[color], boundaryTerm));
					mTerm[color] = null;
				} else {
					// we haven't visited this partition yet, as all previous literals were in A there.
					// increase mMaxColor and mark the boundaryTerm as a new open A-path on the other end.
					assert (mMaxColor == color);
					other.mTerm[color] = boundaryTerm;
					mMaxColor = mColor;
				}
			}
		}

		/**
		 * Open A-paths (or close B-Paths) with the boundary term until there is no A-local child for occur. This means
		 * that we go down the tree until the corresponding literal/term occurs in this partition. For mixed literals we
		 * do nothing, since we are already at the occurrence of one of the literals.
		 *
		 * @param other
		 *            the other path end (usually head)
		 * @param boundaryTerm
		 *            the boundary term
		 * @param occur
		 *            the literal/term whose partition we want to reach.
		 */
		public void openAPath(final PathEnd other, final Term boundaryTerm, final Occurrence occur) {
			/* Go downwards the partition tree, while there is some child where occur is A-local. */
			int child;
			while ((child = getChild(mColor, occur)) >= 0) {
				assert occur.isALocal(child);
				if (mAllInA.get(child)) {
					// While mAllInA is not empty, there are some partitions where all literals are shared.
					// mAllInA lists all partitions where all occurrences on the path are in A.
					// mMaxColor and mColor are kept to the last partition where all the literals
					// occur. So in each child of mMaxColor that is in mAllInA, the whole path is
					// AB shared
					assert (mMaxColor == mColor && mMaxColor == other.mColor);
					mMaxColor = other.mColor = child;
				} else {
					// open a new A-path by remembering the boundary term.
					mTerm[child] = boundaryTerm;
				}
				mColor = child;
			}
		}

		public void closeAPathMixed(final TermVariable mixedVar, final Occurrence occur) {
			// go to the mixed parent and insert the EQ to the boundary term for all partitions on the path.
			while (occur.isBLocal(mColor)) {
				final int color = mColor;
				mColor = getParent(color);
				assert color < mMaxColor;
				mInterpolants[color].add(mTheory.term(Interpolator.EQ, mixedVar, mTerm[color]));
				mTerm[color] = null;
			}
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			String comma = "";
			sb.append(mColor).append(":[");
			for (int i = mColor; i < mMaxColor; i++) {
				sb.append(comma);
				sb.append(mTerm[i]);
				comma = ",";
			}
			sb.append(']');
			return sb.toString();
		}
	}

	public CCInterpolator(final Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
	}

	/**
	 * Compute the parent partition. This is the next partition, whose subtree includes color.
	 */
	private int getParent(final int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child, that is A-local to the occurrence. This function returns
	 * -1 if all children are in B.
	 */
	private int getChild(final int color, final Occurrence occur) {
		/* find A-local child of m_Color */
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	/**
	 * Compute the interpolants for a congruence lemma.
	 *
	 * @param left
	 *            The left application term.
	 * @param right
	 *            The right application term.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateCongruence(final ApplicationTerm left, final ApplicationTerm right) {
		final Term[] interpolants = new Term[mNumInterpolants];
		final Term[] leftParams = left.getParameters();
		final Term[] rightParams = right.getParameters();
		final LitInfo[] paramInfos = new LitInfo[leftParams.length];
		assert left.getFunction() == right.getFunction() && leftParams.length == rightParams.length;

		for (int i = 0; i < leftParams.length; i++) {
			if (leftParams[i] == rightParams[i]) {
				paramInfos[i] = null;
			} else {
				paramInfos[i] = mEqualityOccurrences.get(new SymmetricPair<>(leftParams[i], rightParams[i]));
			}
		}

		for (int part = 0; part < mNumInterpolants; part++) {
			if (mDiseqOccurrences.isBorShared(part)) {
				final ArrayDeque<Term> terms = new ArrayDeque<>(leftParams.length);
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					// Collect A-local literals.
					if (paramInfos[paramNr] != null && paramInfos[paramNr].isALocal(part)) {
						terms.add(mTheory.term("=", leftParams[paramNr], rightParams[paramNr]));
					} else if (paramInfos[paramNr] != null && paramInfos[paramNr].isMixed(part)) {
						// Collect A-local parts in mixed parameter equalities.
						final TermVariable mixedVar = paramInfos[paramNr].getMixedVar();
						final Term sideA = paramInfos[paramNr].getLhsOccur().isALocal(part) ? leftParams[paramNr]
								: rightParams[paramNr];
						terms.add(mTheory.term("=", mixedVar, sideA));
					}
				}
				interpolants[part] = mTheory.and(terms.toArray(new Term[terms.size()]));
			} else if (mDiseqOccurrences.isALocal(part)) {
				final ArrayDeque<Term> terms = new ArrayDeque<>(leftParams.length);
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					// Collect negated B-local literals.
					if (paramInfos[paramNr] != null && paramInfos[paramNr].isBLocal(part)) {
						terms.add(mTheory.not(mTheory.term("=", leftParams[paramNr], rightParams[paramNr])));
					} else if (paramInfos[paramNr] != null && paramInfos[paramNr].isMixed(part)) {
						// Collect B-local parts in mixed parameter equalities.
						final TermVariable mixedVar = paramInfos[paramNr].getMixedVar();
						final Term sideB = paramInfos[paramNr].getLhsOccur().isBLocal(part) ? leftParams[paramNr]
								: rightParams[paramNr];
						terms.add(mTheory.not(mTheory.term("=", mixedVar, sideB)));
					}
				}
				interpolants[part] = mTheory.or(terms.toArray(new Term[terms.size()]));
			} else {
				// the congruence is mixed.  In this case f must be shared and we need to find boundary
				// terms for every parameter.
				final Term[] boundaryTerms = new Term[leftParams.length];
				final boolean isLeftAlocal = mInterpolator.getOccurrence(left).isALocal(part);
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					if (paramInfos[paramNr] == null) {
						// term occurs left and right, so this is obviously shared
						boundaryTerms[paramNr] = leftParams[paramNr];
					} else if (paramInfos[paramNr].isMixed(part)) {
						// mixed case: take mixed var
						boundaryTerms[paramNr] = paramInfos[paramNr].getMixedVar();
					} else if (paramInfos[paramNr].isAorShared(part)) {
						// the argument of the B-local side of the congruence is shared
						boundaryTerms[paramNr] = isLeftAlocal ? rightParams[paramNr] : leftParams[paramNr];
						assert mInterpolator.getOccurrence(boundaryTerms[paramNr]).isAB(part);
					} else {
						// the argument of the A-local side of the congruence is shared, as the argument equality is not
						// mixed
						boundaryTerms[paramNr] = isLeftAlocal ? leftParams[paramNr] : rightParams[paramNr];
						assert mInterpolator.getOccurrence(boundaryTerms[paramNr]).isAB(part);
					}
				}
				final Term sharedTerm = mTheory.term(left.getFunction(), boundaryTerms);
				interpolants[part] = mTheory.term(Interpolator.EQ, mDiseqOccurrences.getMixedVar(), sharedTerm);
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a transitivity lemma.  The path should be in mPath, the disquality in mDiseq.
	 * @return the interpolants
	 */
	@SuppressWarnings("unchecked")
	public Term[] interpolateTransitivity() {
		mInterpolants = new Collection[mNumInterpolants];
		for (int part = 0; part < mNumInterpolants; part++) {
			mInterpolants[part] = new ArrayList<>();
		}

		final Term headTerm = mPath[0];
		final Term tailTerm = mPath[mPath.length - 1];
		final Occurrence headOccur = mInterpolator.getOccurrence(headTerm);
		final Occurrence tailOccur = mInterpolator.getOccurrence(tailTerm);

		mHead = new PathEnd();
		mTail = new PathEnd();
		mMaxColor = mNumInterpolants;
		mAllInA = new BitSet(mNumInterpolants);
		mAllInA.set(0, mNumInterpolants);

		mTail.closeAPath(mHead, null, headOccur);
		mTail.openAPath(mHead, null, headOccur);

		for (int i = 0; i < mPath.length - 1; i++) {
			final Term left = mPath[i];
			final Term right = mPath[i + 1];
			final LitInfo info = mEqualityOccurrences.get(new SymmetricPair<>(left, right));
			mTail.closeAPath(mHead, left, info);
			mTail.openAPath(mHead, left, info);
			if (info.getMixedVar() != null) {
				final Occurrence occ = mInterpolator.getOccurrence(right);
				mTail.closeAPath(mHead, info.getMixedVar(), occ);
				mTail.openAPath(mHead, info.getMixedVar(), occ);
			}
		}
		// add the disequality if present
		if (mDiseqOccurrences != null) {
			mTail.closeAPath(mHead, tailTerm, mDiseqOccurrences);
			mTail.openAPath(mHead, tailTerm, mDiseqOccurrences);
			mHead.closeAPath(mTail, headTerm, mDiseqOccurrences);
			mHead.openAPath(mTail, headTerm, mDiseqOccurrences);

			if (mDiseqOccurrences.getMixedVar() != null) {
				mTail.closeAPathMixed(mDiseqOccurrences.getMixedVar(), headOccur);
				mHead.closeAPathMixed(mDiseqOccurrences.getMixedVar(), tailOccur);
			}
		}
		// close the still open ends where head and tail have different color. The headTerm/tailTerm must be
		// shared in this case.
		while (mHead.mColor != mTail.mColor) {
			while (mHead.mColor < mTail.mColor) {
				mInterpolants[mHead.mColor].add(mTheory.term("=", headTerm, mHead.mTerm[mHead.mColor]));
				mHead.mColor = getParent(mHead.mColor);
			}
			while (mTail.mColor < mHead.mColor) {
				mInterpolants[mTail.mColor].add(mTheory.term("=", mTail.mTerm[mTail.mColor], tailTerm));
				mTail.mColor = getParent(mTail.mColor);
			}
		}
		assert mHead.mColor == mTail.mColor;
		// close the remaining paths, closing the cycles with disequalities or false.
		int color = mHead.mColor;
		while (color < mMaxColor) {
			final int color1 = color;
			mInterpolants[color1].add(mTheory.not(mTheory.term("=", mHead.mTerm[color], mTail.mTerm[color])));
			color = getParent(color);
		}
		while (color < mNumInterpolants) {
			final int color1 = color;
			mInterpolants[color1].add(mTheory.mFalse);
			color = getParent(color);
		}

		// Collect the interpolants
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int part = 0; part < mNumInterpolants; part++) {
			interpolants[part] = mTheory.and(mInterpolants[part].toArray(new Term[mInterpolants[part].size()]));
		}
		return interpolants;
	}

	public Term[] interpolateInstantiation(final InterpolatorClauseInfo proofTermInfo) {
		assert proofTermInfo.getLemmaType().equals(":inst");

		final Term[] interpolants = new Term[mNumInterpolants];

		// The literals in the instantiation lemma.
		final Term[] lits = proofTermInfo.getLiterals();

		// Get occurrence of quantified literal.
		final Term quantLit = mInterpolator.getAtom(lits[0]);
		final Occurrence quantLitInfo = mInterpolator.getAtomOccurenceInfo(quantLit);

		for (int part = 0; part < mNumInterpolants; part++) {
			final ArrayDeque<Term> terms = new ArrayDeque<>(lits.length);
			if (quantLitInfo.isALocal(part)) {
				// Instance is in A.
				for (int i = 0; i < lits.length; i++) {
					final Term atom = mInterpolator.getAtom(lits[i]);
					final LitInfo litInfo = mInterpolator.getAtomOccurenceInfo(atom);
					// Collect all B-local or shared literals. (We do not explicitly negate them, as
					// literals in the lemma are already the negation of literals in the conflict.)
					if (litInfo.isBLocal(part)) {
						terms.add(lits[i]);
					} else if (litInfo.isMixed(part)) {
						final TermVariable mixedVar = litInfo.getMixedVar();
						InterpolatorAtomInfo atomInfo = mInterpolator.getAtomTermInfo(atom);
						if (atomInfo.isCCEquality()) {
							// Collect B-part from splitting mixed literal.
							final Term sideB = litInfo.getLhsOccur().isBLocal(part)
									? ((ApplicationTerm) atom).getParameters()[0]
									: ((ApplicationTerm) atom).getParameters()[1];
	
							if (mInterpolator.isNegatedTerm(lits[i])) {
								terms.add(mTheory.not(mTheory.term(SMTLIBConstants.EQUALS, mixedVar, sideB)));
							} else {
								terms.add(mTheory.term(Interpolator.EQ, mixedVar, sideB));
							}
						} else if (atomInfo.isLAEquality() || atomInfo.isBoundConstraint()) {
							final InterpolatorAffineTerm aPart = litInfo.getAPart(part);
							final InterpolatorAffineTerm bPart = new InterpolatorAffineTerm();
							bPart.add(Rational.ONE, atomInfo.getAffineTerm());
							bPart.add(Rational.MONE, aPart);
							if (atomInfo.isLAEquality()) {
								final Term sideB = bPart.toSMTLib(mTheory, atomInfo.isInt());
								if (mInterpolator.isNegatedTerm(lits[i])) {
									terms.add(mTheory.not(mTheory.term(SMTLIBConstants.EQUALS, mixedVar, sideB)));
								} else {
									terms.add(mTheory.term(Interpolator.EQ, mixedVar, sideB));
								}
							} else {
								bPart.add(Rational.ONE, mixedVar);
								final InfinitesimalNumber epsilon =
										atomInfo.isInt() ? InfinitesimalNumber.ONE : InfinitesimalNumber.EPSILON;
								if (mInterpolator.isNegatedTerm(lits[i])) {
									bPart.mul(Rational.MONE);
									bPart.add(epsilon);
								}
								terms.add(LAInterpolator.createLATerm(bPart, epsilon.negate(), bPart.toLeq0(mInterpolator.mTheory)));
							}
						} else {
							throw new AssertionError();
						}
					}
				}
				if (terms.isEmpty()) {
					interpolants[part] = mTheory.mFalse;
				} else {
					interpolants[part] = mTheory.or(terms.toArray(new Term[terms.size()]));
				}
			} else {
				// Instance is in B.
				for (int i = 0; i < lits.length; i++) {
					final Term atom = mInterpolator.getAtom(lits[i]);
					final LitInfo litInfo = mInterpolator.getAtomOccurenceInfo(atom);
					// Collect all A-local literals. (We need to explicitly negate them,
					// as we need the conflict literal.)
					if (litInfo.isALocal(part)) {
						terms.add(mTheory.not(lits[i]));
					} else if (litInfo.isMixed(part)) {
						// Collect A-part from splitting mixed literal.
						final TermVariable mixedVar = litInfo.getMixedVar();
						InterpolatorAtomInfo atomInfo = mInterpolator.getAtomTermInfo(atom);
						if (atomInfo.isCCEquality()) {
							final Term sideA = litInfo.getLhsOccur().isALocal(part)
									? ((ApplicationTerm) atom).getParameters()[0]
									: ((ApplicationTerm) atom).getParameters()[1];
							if (mInterpolator.isNegatedTerm(lits[i])) {
								terms.add(mTheory.term(SMTLIBConstants.EQUALS, mixedVar, sideA));
							} else {
								terms.add(mTheory.term(Interpolator.EQ, mixedVar, sideA));
							}
						} else if (atomInfo.isLAEquality() || atomInfo.isBoundConstraint()) {
							final InterpolatorAffineTerm aPart = new InterpolatorAffineTerm(litInfo.getAPart(part));
							if (atomInfo.isLAEquality()) {
								final Term sideA = aPart.toSMTLib(mTheory, atomInfo.isInt());
								if (mInterpolator.isNegatedTerm(lits[i])) {
									terms.add(mTheory.term(SMTLIBConstants.EQUALS, mixedVar, sideA));
								} else {
									terms.add(mTheory.term(Interpolator.EQ, mixedVar, sideA));
								}
							} else {
								aPart.add(Rational.MONE, mixedVar);
								final InfinitesimalNumber epsilon =
										atomInfo.isInt() ? InfinitesimalNumber.ONE : InfinitesimalNumber.EPSILON;
								if (!mInterpolator.isNegatedTerm(lits[i])) {
									aPart.mul(Rational.MONE);
								}
								terms.add(LAInterpolator.createLATerm(aPart, epsilon.negate(), aPart.toLeq0(mInterpolator.mTheory)));
							}
						} else {
							throw new AssertionError();
						}
					}
				}
				if (terms.isEmpty()) {
					interpolants[part] = mTheory.mTrue;
				} else {
					interpolants[part] = mTheory.and(terms.toArray(new Term[terms.size()]));
				}
			}
		}
		return interpolants;
	}

	public Term[] computeInterpolants(final InterpolatorClauseInfo proofTermInfo) {
		// Collect the literal infos for all equalities in the clause.
		mEqualityOccurrences = new HashMap<>();
		for (final Term literal : proofTermInfo.getLiterals()) {
			final Term atom = mInterpolator.getAtom(literal);
			if (atom != literal) {
				// negated equality in clause, i.e., positive in conflict.
				final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
				final LitInfo occInfo = mInterpolator.getAtomOccurenceInfo(atom);
				assert atomTermInfo.isCCEquality();
				final ApplicationTerm eq = atomTermInfo.getEquality();
				mEqualityOccurrences.put(new SymmetricPair<>(eq.getParameters()[0], eq.getParameters()[1]), occInfo);
			} else {
				assert mDiseqOccurrences == null;
				mDiseqOccurrences = mInterpolator.getAtomOccurenceInfo(atom);
			}
		}

		mPath = (Term[]) proofTermInfo.getLemmaAnnotation();
		if (proofTermInfo.getLemmaType() == ":cong") {
			return interpolateCongruence((ApplicationTerm) mPath[0], (ApplicationTerm) mPath[1]);
		} else {
			return interpolateTransitivity();
		}
	}

	@Override
	public String toString() {
		return "PathInfo[" + Arrays.toString(mPath) + "," + mHead + ',' + mTail + "," + mMaxColor + "]";
	}
}
