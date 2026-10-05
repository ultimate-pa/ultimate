/*
 * Copyright (C) 2014-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.EQAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Convert a CCAnnotation or an ArrayAnnotation into a proof term using simpler lemmas.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class CCProofGenerator {

	/**
	 * This class is used to keep together paths and their indices (i.e. null for subpaths, and weakpathindex else).
	 */
	private static class IndexedPath {
		private final CCParameter mIndex;
		/** The path nodes as CCParameters (with offsets); a step's offset is justified by an offset equality. */
		private final CCParameter[] mPath;
		/**
		 * The select/const edge justifying this weak path's single weak-congruence step, or {@code null}. See
		 * {@link CCAnnotation#mSelectEdges}: {@code mSelectEdge[0]} is on the {@code mPath[0]} side.
		 */
		private final CCParameter[] mSelectEdge;

		public IndexedPath(final CCParameter index, final CCParameter[] path, final CCParameter[] selectEdge) {
			mIndex = index;
			mPath = path;
			mSelectEdge = selectEdge;
		}

		public CCParameter getIndex() {
			return mIndex;
		}

		public CCParameter[] getPath() {
			return mPath;
		}

		public CCParameter[] getSelectEdge() {
			return mSelectEdge;
		}

		/** The two path ends as a CCParameter pair (with offsets), i.e. the equality this path proves. */
		public SymmetricPair<CCParameter> getPathEndParams() {
			return new SymmetricPair<>(mPath[0], mPath[mPath.length - 1]);
		}

		/** The offset-aware key of the path ends, used to look the path up among shared subpaths. */
		public OffsetPair getPathEnds() {
			return key(getPathEndParams());
		}

		@Override
		public String toString() {
			return mIndex + ": " + Arrays.toString(mPath);
		}
	}

	/**
	 * This class collects the information for an auxiliary lemma that proves an equality literal needed in the main
	 * lemma.
	 *
	 * When converting the array annotation to a proof, we out-source the proves of strong paths like congruences and
	 * select equalities into separate lemmas. We create one proof info for each of these lemmas, that stores the paths
	 * and tracks the other lemmas it needs.
	 *
	 * This class can be used to store the data needed to prove one path or one disequality, respectively. For a
	 * disequality, the required proof data is:
	 * <ul>
	 * <li>the proof paths with path indices (index != null marks weak paths), in particular the first subpath and the
	 * weakpaths for the main disequality, or the congruence paths for auxiliary CC lemmas),</li>
	 * <li>equality and disequality literals from the original clause to explain the single steps in these paths, as
	 * well as literals generated in order to outsource congruences, and</li>
	 * <li>the information which sub-proofs are needed to explain these congruences. For a single path, only the
	 * literals and sub-proofs are necessary.</li>
	 * </ul>
	 */
	private class ProofInfo {

		// Information needed to build the proof graph
		/**
		 * The equality this lemma proves, as a CCParameter pair (with offsets); the offset-free key (see
		 * {@link CCProofGenerator#key}) is used for the lookup maps.
		 */
		private SymmetricPair<CCParameter> mLemmaDiseq;
		/**
		 * The literals this lemma requires for the proof.
		 */
		private final Collection<ProofLiteral> mProofLiterals;
		/**
		 * The paths that this lemma uses.
		 */
		private IndexedPath[] mProofPaths;
		/**
		 * The sub proofs for auxiliary lemmas it depends on.
		 */
		private final Set<ProofInfo> mSubProofs;

		// Information needed to determine the proof order
		private int mNumParents;
		private int mNumVisitedParents;

		public ProofInfo() {
			mLemmaDiseq = null;
			mProofLiterals = new LinkedHashSet<>();
			mSubProofs = new LinkedHashSet<>();
			mNumParents = 0;
			mNumVisitedParents = 0;
		}

		public SymmetricPair<CCParameter> getDiseq() {
			return mLemmaDiseq;
		}

		public Collection<ProofLiteral> getLiterals() {
			return mProofLiterals;
		}

		public IndexedPath[] getPaths() {
			return mProofPaths;
		}

		public Collection<ProofInfo> getSubProofs() {
			return mSubProofs;
		}

		public int getNumParents() {
			return mNumParents;
		}

		public void increaseNumParents() {
			mNumParents++;
		}

		public void increaseVisitedParentsCounter() {
			mNumVisitedParents++;
		}

		public boolean haveVisitedAllParents() {
			return (mNumParents == mNumVisitedParents);
		}

		private void addLiteral(Literal literal) {
			final Theory theory = mProofRules.getTheory();
			mProofLiterals.add(new ProofLiteral(literal.getAtom().getSMTFormula(theory), literal.getSign() > 0));
		}

		private void addAuxLiteral(SymmetricPair<CCParameter> equality, boolean positive) {
			final Term eqTerm = addAuxEquality(equality);
			mProofLiterals.add(new ProofLiteral(eqTerm, positive));
		}

		private void addSubProof(ProofInfo congruence) {
			mSubProofs.add(congruence);
			addAuxLiteral(congruence.getDiseq(), false);
		}

		/**
		 * Collect the proof info for one path.
		 */
		private boolean collectEquality(final SymmetricPair<CCParameter> termPair) {
			final OffsetPair termKey = key(termPair);
			if (isEqualityLiteral(termPair)) {
				// equality literals are just added
				addLiteral(mEqualityLiterals.get(termKey));
				return true;
			} else if (mPathProofMap.containsKey(termKey)) {
				// already created sub proof; add it
				addSubProof(mPathProofMap.get(termKey));
				return true;
			} else {
				// create congruence sub proof
				final ProofInfo congruence = findCongruencePaths(termPair.getFirst(), termPair.getSecond());
				if (congruence == null) {
					return false;
				}
				mPathProofMap.put(termKey, congruence);
				addSubProof(congruence);
				return true;
			}
		}

		/**
		 * Collect the proof info for one path.
		 */
		private void collectStrongPath(final IndexedPath indexedPath) {
			assert (indexedPath.getIndex() == null);
			final CCParameter[] path = indexedPath.getPath();
			// Check cases (i) - (iv) for all term pairs.
			for (int i = 0; i < path.length - 1; i++) {
				final CCParameter firstTerm = path[i];
				final CCParameter secondTerm = path[i + 1];
				final SymmetricPair<CCParameter> termPair = new SymmetricPair<>(firstTerm, secondTerm);
				if (!collectEquality(termPair)) {
					throw new IllegalArgumentException("Cannot explain term pair " + termPair.toString());
				}
			}
		}

		private void collectSelectIndexEquality(final CCParameter select, final CCTerm array, final CCParameter pathIndex) {
			if (!ArrayTheory.isSelectTerm(select) || ArrayTheory.getArrayFromSelect((CCAppTerm) select) != array) {
				throw new AssertionError();
			}
			final CCParameter index = ArrayTheory.getIndexFromSelect((CCAppTerm) select);
			if (!index.equals(pathIndex)) {
				if (!collectEquality(new SymmetricPair<CCParameter>(pathIndex, index))) {
					throw new AssertionError("Cannot find select index equality " + pathIndex + " = " + index);
				}
			}
		}

		/**
		 * Collect the proof info for one path.
		 */
		private void collectWeakPath(final IndexedPath indexedPath) {
			assert (indexedPath.getIndex() != null || mRule == RuleKind.WEAKEQ_EXT || mRule == RuleKind.CONST_WEAKEQ);
			final CCParameter pathIndex = indexedPath.getIndex();
			final CCParameter[] path = indexedPath.getPath();
			// Check cases (i) - (iv) for all term pairs. Array path nodes are offset-free, so we use the structural
			// CCTerms for the array cases and the CCParameters only for the equality (case i).
			for (int i = 0; i < path.length - 1; i++) {
				final CCParameter firstParam = path[i];
				final CCParameter secondParam = path[i + 1];
				// Array terms are offset free, this cast should never fail.
				final CCTerm firstTerm = (CCTerm) firstParam;
				final CCTerm secondTerm = (CCTerm) secondParam;
				final SymmetricPair<CCParameter> termPair = new SymmetricPair<>(firstParam, secondParam);
				// Case (i)
				if (collectEquality(termPair)) {
					continue;
				}
				// Case (ii)
				CCTerm storeTerm = null;
				if (ArrayTheory.isStoreTerm(firstTerm)
						&& ArrayTheory.getArrayFromStore((CCAppTerm) firstTerm) == secondTerm) {
					storeTerm = firstTerm;
				} else if (ArrayTheory.isStoreTerm(secondTerm)
						&& ArrayTheory.getArrayFromStore((CCAppTerm) secondTerm) == firstTerm) {
					storeTerm = secondTerm;
				}
				if (storeTerm != null) {
					// In the main path of weakeq-ext or const-weakeq, no index disequality is needed
					if (pathIndex == null) {
						continue;
					}
					final CCParameter storeIndex = ArrayTheory.getIndexFromStore((CCAppTerm) storeTerm);
					final SymmetricPair<CCParameter> indexPair = new SymmetricPair<>(pathIndex, storeIndex);
					if (isDisequalityLiteral(indexPair)) {
						addLiteral(mEqualityLiterals.get(key(indexPair)));
						continue;
					}
					if (isTrivialDisequality(indexPair)) {
						mTrivialDisequalities.add(addAuxEquality(indexPair));
						addAuxLiteral(indexPair, true);
						continue;
					}
				}
				// Case (iv) select
				if (mRule == RuleKind.WEAKEQ_EXT && pathIndex != null) {
					// Use the select/const edge recorded in the annotation.
					final CCParameter[] selectEdge = indexedPath.getSelectEdge();
					if (selectEdge != null) {
						if (selectEdge[0] != selectEdge[1]) {
							if (!collectEquality(new SymmetricPair<>(selectEdge[0], selectEdge[1]))) {
								throw new AssertionError("Cannot find select edge " + selectEdge);
							}
						}
						if (!isConst(firstTerm, selectEdge[0])) {
							collectSelectIndexEquality(selectEdge[0], firstTerm, pathIndex);
						}
						if (!isConst(secondTerm, selectEdge[1])) {
							collectSelectIndexEquality(selectEdge[1], secondTerm, pathIndex);
						}
						continue;
					}
				}
				// If all cases failed, something is seriously wrong.
				throw new IllegalArgumentException("Cannot explain term pair " + termPair.toString());
			}
		}

		@Override
		public String toString() {
			return "Proof[" + mLemmaDiseq + "]";
		}
	}

	final CCAnnotation mAnnot;
	final CCAnnotation.RuleKind mRule;
	final IndexedPath[] mIndexedPaths;

	// Store the self-built auxiliary equality literals, such that the
	// arguments of the equality are always in the same order.
	private HashMap<OffsetPair, Term> mAuxLiterals;
	private HashMap<OffsetPair, Literal> mEqualityLiterals;
	private HashMap<OffsetPair, ProofInfo> mPathProofMap;
	private LinkedHashSet<OffsetPair> mAllEqualities;
	/** The normalized literals of the trivial disequalities; each of them is proved by its own EQ lemma. */
	private LinkedHashSet<Term> mTrivialDisequalities;
	private ProofRules mProofRules;

	/**
	 * A lookup key identifying an (offset) equality fact between two CCTerms: {@code value(first) == value(second) +
	 * offset}. The maps in this class are keyed on this triple so that two facts sharing offset-free endpoints but
	 * differing in offset — e.g. {@code car(x) = y} (offset 0, a dt-project consequence) and {@code car(x) = y-1}
	 * (offset -1, asserted) in an offset anti-cycle — are kept distinct, while different renderings of the <em>same</em>
	 * fact (e.g. {@code x+5 = y+7} and {@code x+7 = y+9}, both {@code x = y+2}) still collapse to one key. The key is
	 * canonical under swapping the two terms (which negates the offset), mirroring {@link CCTermPairHash}.
	 */
	static final class OffsetPair {
		final CCTerm mFirst;
		final CCTerm mSecond;
		final Rational mOffset;

		OffsetPair(final CCParameter first, final CCParameter second) {
			mFirst = first.getCCTerm();
			mSecond = second.getCCTerm();
			// Structural offset (matching CCEquality.getOffset() used in collectClauseLiterals); the dynamic
			// getOffsetToRep() must not be used here, as disequality endpoints are not in the same class.
			mOffset = second.getOffset().sub(first.getOffset());
		}

		OffsetPair(final CCTerm first, final CCTerm second, final Rational offset) {
			mFirst = first;
			mSecond = second;
			mOffset = offset;
		}

		CCTerm getFirst() {
			return mFirst;
		}

		CCTerm getSecond() {
			return mSecond;
		}

		@Override
		public int hashCode() {
			// symmetric in (first, second); offsetHash is invariant under (first, second, off) -> (second, first, -off)
			return (mFirst.hashCode() ^ mSecond.hashCode()) + CCTermPairHash.offsetHash(mFirst, mSecond, mOffset);
		}

		@Override
		public boolean equals(final Object other) {
			if (this == other) {
				return true;
			}
			if (!(other instanceof OffsetPair)) {
				return false;
			}
			final OffsetPair o = (OffsetPair) other;
			// Both orientations must be tried, not just the first one that matches the two terms: for a degenerate
			// key, where both sides are the same CCTerm, the terms match in either orientation while only one of them
			// matches the offset. Such a key states that a term differs from itself by a constant, e.g. the main
			// disequality of a same-class offset conflict, and (t, t, off) and (t, t, -off) are the same fact - as
			// hashCode (via the offset.abs() fallback in offsetHash) and addAuxEquality (which normalizes the sign of
			// the offset) already treat them.
			if (mFirst == o.mFirst && mSecond == o.mSecond && mOffset.equals(o.mOffset)) {
				return true;
			}
			return mFirst == o.mSecond && mSecond == o.mFirst && mOffset.equals(o.mOffset.negate());
		}

		@Override
		public String toString() {
			return mOffset.equals(Rational.ZERO) ? "(" + mFirst + "," + mSecond + ")"
					: "(" + mFirst + "," + mSecond + "+" + mOffset + ")";
		}
	}

	/**
	 * The offset-aware key of a CCParameter equality: {@code value(first) == value(second) + offset}, where
	 * {@code offset = second.getOffset() - first.getOffset()} is the constant offset between the two underlying CCTerms.
	 * See {@link OffsetPair}.
	 */
	static OffsetPair key(final SymmetricPair<CCParameter> pair) {
		final CCParameter first = pair.getFirst();
		final CCParameter second = pair.getSecond();
		return new OffsetPair(first, second);
	}

	public CCProofGenerator(final CCAnnotation arrayAnnot) {
		mAnnot = arrayAnnot;
		mRule = arrayAnnot.mRule;
		mIndexedPaths = new IndexedPath[arrayAnnot.getParamPaths().length];
		for (int i = 0; i < mIndexedPaths.length; i++) {
			mIndexedPaths[i] = new IndexedPath(arrayAnnot.getWeakIndices()[i], arrayAnnot.getParamPaths()[i],
					arrayAnnot.getSelectEdges()[i]);
		}
	}

	/**
	 * Convert the array annotation into a term suitable to add to the proof tree. The output is an array lemma where
	 * all congruences are explained by auxiliary CC lemmas in a hyper-resolution step.
	 *
	 * @param clause
	 *            The clause containing this annotation.
	 * @param theory
	 *            The term unifier.
	 * @return the proof term in form of a resolution step of the central array lemma and the auxiliary lemmas which are
	 *         obtained from subpaths explaining congruences in the main lemma - or, if there are no congruences, just
	 *         the array lemma.
	 */
	public Term toTerm(final Clause clause, final ProofRules proofRules) {
		mProofRules = proofRules;
		mAllEqualities = new LinkedHashSet<>();
		mTrivialDisequalities = new LinkedHashSet<>();
		mAuxLiterals = new HashMap<>();
		// Store all clause literals
		collectClauseLiterals(clause);
		// Create a proof info for each sub path that isn't an asserted equality.
		collectStrongEqualities();

		// Collect the paths needed to prove the main disequality
		final ProofInfo mainInfo = findMainPaths();
		if (mAnnot.mDiseq != null) {
			final SymmetricPair<CCParameter> mainDiseq = mAnnot.mDiseq;
			if (!isDisequalityLiteral(mainDiseq)) {
				assert isTrivialDisequality(mainDiseq);
				mTrivialDisequalities.add(addAuxEquality(mainDiseq));
			}
			mainInfo.mLemmaDiseq = mainDiseq;
			mPathProofMap.put(key(mainDiseq), mainInfo);
		} else {
			assert mAnnot.mRule == RuleKind.DT_CASES || mAnnot.mRule == RuleKind.DT_UNIQUE
					|| mAnnot.mRule == RuleKind.DT_DISJOINT
					|| mAnnot.mRule == RuleKind.DT_CYCLE : "Rule needs a disequality";
		}

		// set the parent counter, to facilitate topological order
		determineAllNumParents(mainInfo);
		// Determine the order of the auxiliary lemmas in the resolution tree.
		final ArrayList<ProofInfo> proofOrder = determineProofOrder(mainInfo);

		// Build the final proof term
		return buildProofTerm(clause, proofRules, proofOrder);
	}

	/**
	 * Store all original clause literals as a SymmetricPair for better comparison, mapped to the original literal.
	 */
	private void collectClauseLiterals(final Clause clause) {
		mEqualityLiterals = new HashMap<>();
		for (int i = 0; i < clause.getSize(); i++) {
			final Literal literal = clause.getLiteral(i);
			final CCEquality atom = (CCEquality) literal.getAtom();
			// key on the actual offset so two literals between the same terms but with different offsets
			// (e.g. car(x)=y and car(x)=y-1 in an offset anti-cycle) stay distinct.
			final OffsetPair pair = new OffsetPair(atom.getLhs(), atom.getRhs(), atom.getOffset());
			mEqualityLiterals.put(pair, literal);
			if (literal.getSign() < 0) {
				/* equality in conflict (negated in clause) */
				mAllEqualities.add(pair);
			}
		}
	}

	/**
	 * Build a map from the pairs of subpath ends to the array containing the whole path. This helps to find select and
	 * congruence paths more efficiently by comparing SymmetricPairs.
	 */
	private void collectStrongEqualities() {
		mPathProofMap = new HashMap<>();
		/* collect them backwards, so that the dependent proof infos are already created */
		for (int i = mIndexedPaths.length - 1; i >= 0; i--) {
			final IndexedPath indexedPath = mIndexedPaths[i];
			// check if this is a strong equality. Note that the first sub path of WEAKEQ_EXT and CONST_WEAKEQ is
			// never a strong equality, even though its weak index is null.
			if (indexedPath.getIndex() == null
					&& ((mRule != RuleKind.WEAKEQ_EXT && mRule != RuleKind.CONST_WEAKEQ) || i > 0)) {
				final CCParameter[] path = indexedPath.getPath();
				final SymmetricPair<CCParameter> pathEndParams = indexedPath.getPathEndParams();
				final OffsetPair pathEnds = key(pathEndParams);
				if (mAllEqualities.add(pathEnds) && !mPathProofMap.containsKey(pathEnds)) {
					if (path.length == 2) {
						// A path of length 2 must be a congruence, otherwise we would not be able to explain it
						final ProofInfo congruence = findCongruencePaths(path[0], path[1]);
						assert congruence != null;
						mPathProofMap.put(pathEnds, congruence);
					} else {
						final ProofInfo pathInfo = new ProofInfo();
						pathInfo.mLemmaDiseq = pathEndParams;
						pathInfo.mProofPaths = new IndexedPath[] { indexedPath };
						pathInfo.collectStrongPath(indexedPath);
						mPathProofMap.put(pathEnds, pathInfo);
					}
				}
			}
		}
	}

	/**
	 * Collect all paths needed to prove the main disequality, i.e. the main path which starts with one side of the main
	 * diseq and ends with the other (for weakeq-ext) or which starts with the select index of one side of the main
	 * diseq and ends with the other select index (for read-over-weakeq), and all weakpaths.
	 */
	private ProofInfo findMainPaths() {
		final ProofInfo mainProof = new ProofInfo();
		switch (mRule) {
		case TRANS:
		case CONG:
			// The main path was already collected, just return it.
			return mPathProofMap.get(mIndexedPaths[0].getPathEnds());
		case READ_OVER_WEAKEQ: {
			// collect index equality and the weak path
			final SymmetricPair<CCParameter> selectEquality = mAnnot.mDiseq;
			assert ArrayTheory.isSelectTerm(selectEquality.getFirst())
					&& ArrayTheory.isSelectTerm(selectEquality.getSecond());
			// collect the index equality
			final CCParameter idx1 = ArrayTheory.getIndexFromSelect((CCAppTerm) selectEquality.getFirst());
			final CCParameter idx2 = ArrayTheory.getIndexFromSelect((CCAppTerm) selectEquality.getSecond());
			if (!idx1.equals(idx2)) {
				mainProof.collectEquality(new SymmetricPair<>(idx1, idx2));
			}
			// Only a weak path, which must be the first path
			assert mIndexedPaths[0].getIndex() != null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			mainProof.mProofPaths = new IndexedPath[] { mIndexedPaths[0] };
			break;
		}
		case READ_CONST_WEAKEQ:
			// only a weak path, which must be the first path
			assert mIndexedPaths[0].getIndex() != null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			mainProof.mProofPaths = new IndexedPath[] { mIndexedPaths[0] };
			break;
		case CONST_WEAKEQ:
			// only a weak path without index from const to const
			assert mIndexedPaths[0].getIndex() == null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			mainProof.mProofPaths = new IndexedPath[] { mIndexedPaths[0] };
			break;
		case WEAKEQ_EXT: {
			// starts with a weak path without index, followed by other weak paths.
			final ArrayList<IndexedPath> mPaths = new ArrayList<>();
			assert mIndexedPaths[0].getIndex() == null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			mPaths.add(mIndexedPaths[0]);
			for (int i = 0; i < mIndexedPaths.length; i++) {
				if (mIndexedPaths[i].getIndex() != null) {
					mainProof.collectWeakPath(mIndexedPaths[i]);
					mPaths.add(mIndexedPaths[i]);
				}
			}
			mainProof.mProofPaths = mPaths.toArray(new IndexedPath[mPaths.size()]);
			break;
		}
		case DT_CASES:
		case DT_CONSTRUCTOR:
		case DT_CYCLE:
		case DT_DISJOINT:
		case DT_INJECTIVE:
		case DT_PROJECT:
		case DT_TESTER:
		case DT_UNIQUE:
			for (final SymmetricPair<CCTerm> dependentEq : mAnnot.mDTLemma.getReason()) {
				// datatype lemma reasons are offset-free
				mainProof.collectEquality(new SymmetricPair<CCParameter>(dependentEq.getFirst(), dependentEq.getSecond()));
			}
			mainProof.mProofPaths = new IndexedPath[0];
			break;
		}
		return mainProof;
	}

	/**
	 * Set mNumParents in the proof info for all nodes of a given proof graph.
	 */
	private void determineAllNumParents(final ProofInfo mainInfo) {
		// Traverse the proof graph and count the parents, skip already visited nodes.
		final ArrayDeque<ProofInfo> todo = new ArrayDeque<>();
		todo.add(mainInfo);
		while (!todo.isEmpty()) {
			final ProofInfo proofInfo = todo.removeFirst();
			if (proofInfo.getNumParents() == 0) {
				todo.addAll(proofInfo.mSubProofs);
			}
			proofInfo.increaseNumParents();
		}
	}

	/**
	 * Determine the order of the resolution tree. Start with the main lemma, represented by the main disequality, and
	 * continue with its successor nodes. A node representing an auxiliary lemma can appear in the proof order only
	 * after all its parent nodes.
	 */
	private ArrayList<ProofInfo> determineProofOrder(final ProofInfo mainInfo) {
		final ArrayList<ProofInfo> proofOrder = new ArrayList<>();
		final ArrayDeque<ProofInfo> todo = new ArrayDeque<>();
		todo.add(mainInfo);
		while (!todo.isEmpty()) {
			final ProofInfo nodeInfo = todo.removeFirst();
			nodeInfo.increaseVisitedParentsCounter();
			if (nodeInfo.haveVisitedAllParents()) {
				proofOrder.add(nodeInfo);
				todo.addAll(nodeInfo.getSubProofs());
			}
		}
		return proofOrder;
	}

	private Term addAuxEquality(SymmetricPair<CCParameter> equality) {
		final OffsetPair eqKey = key(equality);
		if (!mAuxLiterals.containsKey(eqKey)) {
			final Theory theory = mProofRules.getTheory();
			/*
			 * Normalize the equality the same way CCEquality.getSMTFormula() renders an offset equality, i.e. as
			 * (= offset-free-lhs (+ offset-free-rhs offset)), so that all equalities stating the same affine fact
			 * produce the same term. For a degenerate key, where both sides have the same offset-free term, the sign
			 * of the offset is not determined by the order of the sides, so it is normalized to be positive; this way
			 * two trivial disequalities like 1 != 0 and 1 != 2 share the same clause literal (= 0 1).
			 */
			Term lhs = eqKey.getFirst().getFlatTerm();
			Term rhs = eqKey.getSecond().getFlatTerm();
			Rational offset = eqKey.mOffset;
			final boolean needsSwap;
			if (lhs == rhs) {
				// the order of the sides carries no information; normalize the offset to be positive
				needsSwap = offset.signum() < 0;
			} else {
				// to make cc equalities different from la equalities, ensure that rhs is not a constant.
				needsSwap = rhs.getSort().isNumericSort() && rhs instanceof ConstantTerm
						&& ((ConstantTerm) rhs).getValue().equals(Rational.ZERO);
			}
			if (needsSwap) {
				// (= lhs (+ rhs offset)) states the same fact as (= rhs (+ lhs -offset))
				final Term swapped = lhs;
				lhs = rhs;
				rhs = swapped;
				offset = offset.negate();
			}
			mAuxLiterals.put(eqKey, theory.term("=", lhs, CCParameter.addConstant(rhs, offset)));
		}
		return mAuxLiterals.get(eqKey);
	}

	private Term buildLemma(final ProofRules proofRules, RuleKind rule, final ProofInfo info, final Term mainEq) {
		final Theory theory = proofRules.getTheory();
		// Collect the new clause literals.
		final Set<ProofLiteral> clause = new LinkedHashSet<>(info.getLiterals().size() + (mainEq != null ? 1 : 0));
		if (mainEq != null) {
			// First the (positive) diseq literal
			clause.add(new ProofLiteral(mainEq, true));
		}
		// then the other literals, there may also be other positive literals.
		for (final ProofLiteral entry : info.getLiterals()) {
			clause.add(entry);
		}
		assert clause.size() == info.getLiterals().size() + (mainEq != null ? 1 : 0);
		final ProofLiteral[] args = clause.toArray(new ProofLiteral[clause.size()]);

		final Object[] subannots;
		if (rule == RuleKind.CONG) {
			// this is a transitivity or congruence lemma
			assert info.getPaths().length == 1;
			final CCParameter[] path = info.getPaths()[0].getPath();
			final Term[] subs = new Term[path.length];
			for (int j = 0; j < path.length; ++j) {
				subs[j] = path[j].getFlatTerm();
			}
			rule = subs.length == 2 ? RuleKind.CONG : RuleKind.TRANS;
			subannots = subs;
		} else {
			final IndexedPath[] paths = info.getPaths();
			final SymmetricPair<CCParameter> infoDiseq = info.getDiseq();
			Object[] lemmaAnnot = new Object[0];
			if (mAnnot.mDTLemma != null && mAnnot.mDTLemma.getAnnotation() != null) {
				lemmaAnnot = mAnnot.mDTLemma.getAnnotation();
			}
			subannots = new Object[2 * paths.length + (infoDiseq == null ? 0 : 1) + lemmaAnnot.length];
			int k = 0;
			if (infoDiseq != null) {
				final Term diseqTerm = theory.term(SMTLIBConstants.EQUALS, infoDiseq.getFirst().getFlatTerm(),
						infoDiseq.getSecond().getFlatTerm());
				subannots[k++] = diseqTerm;
			}
			for (final Object annot : lemmaAnnot) {
				subannots[k++] = annot;
			}
			for (final IndexedPath p : paths) {
				final CCParameter index = p.getIndex();
				final CCParameter[] path = p.getPath();
				final Term[] subs = new Term[path.length];
				for (int j = 0; j < path.length; ++j) {
					subs[j] = path[j].getFlatTerm();
				}
				if (index == null) {
					subannots[k++] = ":subpath";
					subannots[k++] = subs;
				} else {
					subannots[k++] = ":weakpath";
					final CCParameter[] edge = p.getSelectEdge();
					if (edge == null) {
						subannots[k++] = new Object[] { index.getFlatTerm(), subs };
					} else {
						// Append the select/const edge {left, right} that justifies this weak path's weak-congruence
						// step; left is on the subs[0] side. Consumers that predate this element ignore it (they read
						// only [0] and [1]).
						subannots[k++] = new Object[] { index.getFlatTerm(), subs,
								new Object[] { edge[0].getFlatTerm(), edge[1].getFlatTerm() } };
					}
				}
			}
		}
		final Annotation[] annots = new Annotation[] { new Annotation(rule.getKind(), subannots) };
		return proofRules.oracle(args, annots);
	}

	/**
	 * Build the proof term in the form of a resolution step of the main lemma resolved with the auxiliary lemmas in the
	 * order determined by proofOrder.
	 */
	private Term buildProofTerm(final Clause clause, final ProofRules proofRules,
			final ArrayList<ProofInfo> proofOrder) {

		final Theory theory = proofRules.getTheory();

		// Build main lemma
		final ProofInfo mainInfo = proofOrder.get(0);
		assert mainInfo.getDiseq() == mAnnot.getDiseq();
		// The equality proved by the lemma. It is null for rules without main equality
		final Term mainEq = mainInfo.getDiseq() == null ? null
				: isDisequalityLiteral(mainInfo.getDiseq())
						? mEqualityLiterals.get(key(mainInfo.getDiseq())).getSMTFormula(theory)
						: mAuxLiterals.get(key(mainInfo.getDiseq()));
		Term proof = buildLemma(proofRules, mRule, mainInfo, mainEq);
		// Resolve with sub-lemmas.
		for (int lemmaNo = 1; lemmaNo < proofOrder.size(); lemmaNo++) {
			// Build the lemma clause.
			final ProofInfo info = proofOrder.get(lemmaNo);
			// auxLiteral should already have been created by the lemma that needs it.
			assert mAuxLiterals.containsKey(key(info.getDiseq()));
			final Term provedEq = mAuxLiterals.get(key(info.getDiseq()));

			// Build lemma annotations.
			final Term lemma = buildLemma(proofRules, RuleKind.CONG, info, provedEq);
			proof = proofRules.resolutionRule(provedEq, lemma, proof);
		}
		for (final Term provedEq : mTrivialDisequalities) {
			final ProofLiteral[] proofLits = new ProofLiteral[] { new ProofLiteral(provedEq, false) };
			final Term diseqLemma = proofRules.oracle(proofLits, EQAnnotation.getAnnotation());
			proof = proofRules.resolutionRule(provedEq, proof, diseqLemma);
		}
		return proof;
	}

	private boolean isEqualityLiteral(final SymmetricPair<CCParameter> termPair) {
		final OffsetPair k = key(termPair);
		return mEqualityLiterals.containsKey(k) && mEqualityLiterals.get(k).getSign() < 0;
	}

	private boolean isDisequalityLiteral(final SymmetricPair<CCParameter> termPair) {
		final OffsetPair k = key(termPair);
		return mEqualityLiterals.containsKey(k) && mEqualityLiterals.get(k).getSign() > 0;
	}

	private boolean isTrivialDisequality(final SymmetricPair<CCParameter> termPair) {
		// use the CCParameter flat terms so an offset clash (e.g. x+2 vs x+5) is detected
		final Polynomial smtAffine = new Polynomial(termPair.getFirst().getFlatTerm());
		smtAffine.add(Rational.MONE, termPair.getSecond().getFlatTerm());
		if (smtAffine.isConstant()) {
			return smtAffine.getConstant() != Rational.ZERO;
		}
		return smtAffine.isAllIntSummands() && !smtAffine.getConstant().div(smtAffine.getGcd()).isIntegral();
	}

	/**
	 * Find argument paths for a congruence. These may also be literals from the original clause. Note that a function
	 * can have several arguments, and a path is needed for each of them!
	 *
	 * @return The argument paths, if they exist for all arguments, or null to indicate that the termpair is not a
	 *         congruence.
	 */
	private ProofInfo findCongruencePaths(final CCParameter first, final CCParameter second) {
		final CCTerm firstTerm = first.getCCTerm();
		final CCTerm secondTerm = second.getCCTerm();
		if (!(firstTerm instanceof CCAppTerm) || !(secondTerm instanceof CCAppTerm)
				|| !first.getOffset().equals(second.getOffset())) {
			// This is not a congruence
			return null;
		}
		final CCAppTerm firstApp = (CCAppTerm) firstTerm;
		final CCAppTerm secondApp = (CCAppTerm) secondTerm;
		if (firstApp.getFunctionSymbol() != secondApp.getFunctionSymbol()) {
			// This is not a congruence
			return null;
		}

		final ProofInfo proofInfo = new ProofInfo();
		// A congruence is offset-free: f(a) and f(b) have equal value once their arguments are equal, so the two app
		// terms always sit at the same offset on a path and the congruence proves the offset-free f(a) = f(b). Render
		// the lemma and its (length-2) proof path with the offset-free app terms; the surrounding :trans/:cong checker
		// absorbs the common constant shift. Carrying the offset (e.g. (= (+ f(a) -1) (+ f(b) -1)) :cong) is not a valid
		// single congruence — that step is over +, not over f — and breaks the lowlevel proof. The diseq key is offset
		// invariant (the offset cancels in the difference), so all lookups are unaffected.
		proofInfo.mLemmaDiseq = new SymmetricPair<>(firstTerm, secondTerm);
		proofInfo.mProofPaths =
				new IndexedPath[] { new IndexedPath(null, new CCParameter[] { firstTerm, secondTerm }, null) };

		assert firstApp.getArgCount() == secondApp.getArgCount();
		for (int i = 0; i < firstApp.getArgCount(); i++) {
			final CCParameter firstArg = firstApp.getArgParam(i);
			final CCParameter secondArg = secondApp.getArgParam(i);
			// Resolve on the exact CCParameter equality of the arguments. Offset-free this is a direct literal or
			// subpath lookup; the lookup maps are keyed offset-free so a shared offset edge is reused.
			// A shifted version of the same argument equality needs no bridging lemma: the key holds the offset
			// between the two CCTerms, i.e. the fact itself, not the offsets it happens to be rendered with. For
			// f(x,x+2) = f(y+2,y+4) both arguments key on (x, y, 2), and the (x, y) subpath, whose ends are rendered
			// so that they denote the same value, keys on 2 as well.
			if (firstArg.getCCTerm() != secondArg.getCCTerm()) {
				final SymmetricPair<CCParameter> argPair = new SymmetricPair<>(firstArg, secondArg);
				final OffsetPair argKey = key(argPair);
				if (isEqualityLiteral(argPair)) {
					proofInfo.addLiteral(mEqualityLiterals.get(argKey));
				} else if (mPathProofMap.containsKey(argKey)) {
					proofInfo.addSubProof(mPathProofMap.get(argKey));
				} else {
					// If no path was found for the arguments, termpair is not a congruence!
					return null;
				}
			}
		}
		return proofInfo;
	}

	/**
	 * Check if array is an application of const on value
	 */
	private boolean isConst(final CCParameter array, final CCParameter value) {
		return (ArrayTheory.isConstTerm(array) && ArrayTheory.getValueFromConst((CCAppTerm) array).equals(value));
	}
}
