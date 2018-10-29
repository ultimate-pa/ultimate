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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
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
		private final CCTerm mIndex;
		private final CCTerm[] mPath;

		public IndexedPath(final CCTerm index, final CCTerm[] path) {
			mIndex = index;
			mPath = path;
		}

		public CCTerm getIndex() {
			return mIndex;
		}

		public CCTerm[] getPath() {
			return mPath;
		}

		public String toString() {
			return mIndex + ": " + Arrays.toString(mPath);
		}
	}

	/**
	 * This class is used to represent a select edge and select-const edges in weak congruences.
	 */
	private static class SelectEdge {
		private final CCTerm mLeft;
		private final CCTerm mRight;

		public SelectEdge(CCTerm left, CCTerm right) {
			this.mLeft = left;
			this.mRight = right;
		}

		public SymmetricPair<CCTerm> toSymmetricPair() {
			return new SymmetricPair<CCTerm>(mLeft, mRight);
		}

		public CCTerm getLeft() {
			return mLeft;
		}

		public CCTerm getRight() {
			return mRight;
		}

		public String toString() {
			return mLeft + " <-> " + mRight;
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
		 * The equality this lemma proves.
		 */
		private SymmetricPair<CCTerm> mLemmaDiseq;
		/**
		 * The literals this lemma requires for the proof.
		 */
		private final HashMap<SymmetricPair<CCTerm>, Literal> mProofLiterals;
		/**
		 * The paths that this lemma uses.
		 */
		private final LinkedHashSet<IndexedPath> mProofPaths;
		/**
		 * The sub proofs for auxiliary lemmas it depends on.
		 */
		private final HashMap<SymmetricPair<CCTerm>, ProofInfo> mSubProofs;

		// Information needed to determine the proof order
		private int mNumParents;
		private int mNumVisitedParents;

		public ProofInfo() {
			mLemmaDiseq = null;
			mProofLiterals = new HashMap<>();
			mProofPaths = new LinkedHashSet<>();
			mSubProofs = new HashMap<>();
			mNumParents = 0;
			mNumVisitedParents = 0;
		}

		public SymmetricPair<CCTerm> getDiseq() {
			return mLemmaDiseq;
		}

		public HashMap<SymmetricPair<CCTerm>, Literal> getLiterals() {
			return mProofLiterals;
		}

		public LinkedHashSet<IndexedPath> getPaths() {
			return mProofPaths;
		}

		public HashMap<SymmetricPair<CCTerm>, ProofInfo> getSubProofs() {
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

		/**
		 * Collect the proof info for one path.
		 */
		private boolean collectEquality(final SymmetricPair<CCTerm> termPair) {
			if (isEqualityLiteral(termPair)) {
				// equality literals are just added
				mProofLiterals.put(termPair, mEqualityLiterals.get(termPair));
				return true;
			} else if (mPathProofMap.containsKey(termPair)) {
				// already created sub proof; add it
				mSubProofs.put(termPair, mPathProofMap.get(termPair));
				return true;
			} else {
				// create congruence sub proof
				final ProofInfo congruence = findCongruencePaths(termPair.getFirst(), termPair.getSecond());
				if (congruence == null) {
					return false;
				}
				mSubProofs.put(termPair, congruence);
				return true;
			}
		}

		/**
		 * Collect the proof info for one path.
		 */
		private void collectStrongPath(final IndexedPath indexedPath) {
			assert (indexedPath.getIndex() == null);
			mProofPaths.add(indexedPath);
			final CCTerm[] path = indexedPath.getPath();
			// Check cases (i) - (iv) for all term pairs.
			for (int i = 0; i < path.length - 1; i++) {
				final CCTerm firstTerm = path[i];
				final CCTerm secondTerm = path[i + 1];
				final SymmetricPair<CCTerm> termPair = new SymmetricPair<>(firstTerm, secondTerm);
				if (!collectEquality(termPair)) {
					throw new IllegalArgumentException("Cannot explain term pair " + termPair.toString());
				}
			}
		}

		private void collectSelectIndexEquality(final CCTerm select, CCTerm pathIndex) {
			if (isSelectTerm(select)) {
				final CCTerm index = ArrayTheory.getIndexFromSelect((CCAppTerm) select);
				if (index != pathIndex) {
					if (!collectEquality(new SymmetricPair<>(pathIndex, index))) {
						throw new AssertionError("Cannot find select index equality " + pathIndex + " = " + index);
					}
				}
			}
		}

		/**
		 * Collect the proof info for one path.
		 */
		private void collectWeakPath(final IndexedPath indexedPath) {
			assert (indexedPath.getIndex() != null || mRule == RuleKind.WEAKEQ_EXT || mRule == RuleKind.CONST_WEAKEQ);
			mProofPaths.add(indexedPath);
			final CCTerm pathIndex = indexedPath.getIndex();
			final CCTerm[] path = indexedPath.getPath();
			// Check cases (i) - (iv) for all term pairs.
			for (int i = 0; i < path.length - 1; i++) {
				final CCTerm firstTerm = path[i];
				final CCTerm secondTerm = path[i + 1];
				final SymmetricPair<CCTerm> termPair = new SymmetricPair<>(firstTerm, secondTerm);
				// Case (i)
				if (collectEquality(termPair)) {
					continue;
				}
				// Case (ii)
				CCTerm storeTerm = null;
				if (isStoreTerm(firstTerm) && ArrayTheory.getArrayFromStore((CCAppTerm) firstTerm) == secondTerm) {
					storeTerm = firstTerm;
				} else if (isStoreTerm(secondTerm)
						&& ArrayTheory.getArrayFromStore((CCAppTerm) secondTerm) == firstTerm) {
					storeTerm = secondTerm;
				}
				if (storeTerm != null) {
					// In the main path of weakeq-ext or const-weakeq, no index disequality is needed
					if (pathIndex == null) {
						continue;
					}
					final CCTerm storeIndex = ArrayTheory.getIndexFromStore((CCAppTerm) storeTerm);
					final SymmetricPair<CCTerm> indexPair = new SymmetricPair<>(pathIndex, storeIndex);
					if (isDisequalityLiteral(indexPair)) {
						mProofLiterals.put(indexPair, mEqualityLiterals.get(indexPair));
						continue;
					}
					if (isTrivialDisequality(indexPair)) {
						continue;
					}
				}
				// Case (iv) select
				if (mRule == RuleKind.WEAKEQ_EXT && pathIndex != null) {
					SelectEdge selectEdge = findSelectPath(termPair, pathIndex);
					if (selectEdge != null) {
						if (selectEdge.getLeft() != selectEdge.getRight()) {
							if (!collectEquality(selectEdge.toSymmetricPair())) {
								throw new AssertionError("Cannot find select edge " + selectEdge);
							}
						}
						if (!isConst(firstTerm, selectEdge.getLeft())) {
							collectSelectIndexEquality(selectEdge.getLeft(), pathIndex);
						}
						if (!isConst(secondTerm, selectEdge.getRight())) {
							collectSelectIndexEquality(selectEdge.getRight(), pathIndex);
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

	private HashMap<SymmetricPair<CCTerm>, Literal> mEqualityLiterals;
	private HashMap<SymmetricPair<CCTerm>, ProofInfo> mPathProofMap;
	private HashSet<SymmetricPair<CCTerm>> mAllEqualities;

	public CCProofGenerator(final CCAnnotation arrayAnnot) {
		mAnnot = arrayAnnot;
		mRule = arrayAnnot.mRule;
		mIndexedPaths = new IndexedPath[arrayAnnot.getPaths().length];
		for (int i = 0; i < mIndexedPaths.length; i++) {
			mIndexedPaths[i] = new IndexedPath(arrayAnnot.getWeakIndices()[i], arrayAnnot.getPaths()[i]);
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
	public Term toTerm(final Clause clause, final Theory theory) {
		mAllEqualities = new HashSet<>();
		// Store all clause literals
		collectClauseLiterals(clause);
		// Create a proof info for each sub path that isn't an asserted equality.
		collectStrongEqualities();

		// Collect the paths needed to prove the main disequality
		final ProofInfo mainInfo = findMainPaths();
		assert mAnnot.mDiseq != null;
		final SymmetricPair<CCTerm> mainDiseq = mAnnot.mDiseq;
		assert isDisequalityLiteral(mainDiseq) || isTrivialDisequality(mainDiseq);
		mainInfo.mLemmaDiseq = mainDiseq;
		mPathProofMap.put(mainDiseq, mainInfo);

		// set the parent counter, to facilitate topological order
		determineAllNumParents(mainInfo);
		// Determine the order of the auxiliary lemmas in the resolution tree.
		final ArrayList<ProofInfo> proofOrder = determineProofOrder(mainInfo);

		// Build the final proof term
		return buildProofTerm(clause, theory, proofOrder);
	}

	/**
	 * Store all original clause literals as a SymmetricPair for better comparison, mapped to the original literal.
	 */
	private void collectClauseLiterals(final Clause clause) {
		mEqualityLiterals = new HashMap<>();
		for (int i = 0; i < clause.getSize(); i++) {
			Literal literal = clause.getLiteral(i);
			CCEquality atom = (CCEquality) literal.getAtom();
			SymmetricPair<CCTerm> pair = new SymmetricPair<>(atom.getLhs(), atom.getRhs());
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
				final CCTerm[] path = indexedPath.getPath();
				final SymmetricPair<CCTerm> pathEnds = new SymmetricPair<>(path[0], path[path.length - 1]);
				if (mAllEqualities.add(pathEnds)) {
					final ProofInfo pathInfo = new ProofInfo();
					pathInfo.mLemmaDiseq = pathEnds;
					pathInfo.collectStrongPath(indexedPath);
					mPathProofMap.put(pathEnds, pathInfo);
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
		case CC:
			mainProof.collectStrongPath(mIndexedPaths[0]);
			break;
		case WEAKEQ_EXT:
			assert mIndexedPaths[0].getIndex() == null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			break;
		case READ_OVER_WEAKEQ: {
			IndexedPath firstPath = mIndexedPaths[0];
			if (firstPath.getIndex() == null) {
				// for read-over-weakeq, create a short first path
				final CCTerm[] path = firstPath.getPath();
				if (path.length > 2) {
					firstPath = new IndexedPath(null, new CCTerm[] { path[0], path[path.length - 1] });
				}
				// TODO: should we only collect equality?
				mainProof.collectStrongPath(firstPath);
			}
			break;
		}
		case READ_CONST_WEAKEQ:
			break;
		case CONST_WEAKEQ:
			assert mIndexedPaths[0].getIndex() == null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			break;
		}
		for (int i = 0; i < mIndexedPaths.length; i++) {
			if (mIndexedPaths[i].getIndex() != null) {
				mainProof.collectWeakPath(mIndexedPaths[i]);
			}
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
				todo.addAll(proofInfo.mSubProofs.values());
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
				todo.addAll(nodeInfo.getSubProofs().values());
			}
		}
		return proofOrder;
	}

	private Term buildLemma(Theory theory, RuleKind rule, ProofInfo info, Term diseq, boolean isTrivialDiseq,
			HashMap<SymmetricPair<CCTerm>, Term> auxLiterals) {
		// Collect the new clause literals.
		final Term[] args = new Term[info.getLiterals().size() + (isTrivialDiseq ? 0 : 1) + info.getSubProofs().size()];
		int i = 0;
		if (!isTrivialDiseq) {
			// First the (positive) diseq literal
			args[i++] = theory.annotatedTerm(CCEquality.QUOTED_CC, diseq);
		}
		// then the other literals, there may also be other positive literals.
		for (final Map.Entry<SymmetricPair<CCTerm>, Literal> entry : info.getLiterals().entrySet()) {
			Term arg = entry.getValue().getAtom().getSMTFormula(theory, true);
			if (entry.getValue().getSign() < 0) {
				arg = theory.not(arg);
			}
			args[i++] = arg;
		}
		for (final Map.Entry<SymmetricPair<CCTerm>, ProofInfo> entry : info.getSubProofs().entrySet()) {
			if (!auxLiterals.containsKey(entry.getKey())) {
				final Term lhs = entry.getKey().getFirst().toSMTTerm(theory);
				final Term rhs = entry.getKey().getSecond().toSMTTerm(theory);
				auxLiterals.put(entry.getKey(), theory.term("=", lhs, rhs));
			}
			/* these are always negated equalities */
			Term arg = theory.annotatedTerm(CCEquality.QUOTED_CC, auxLiterals.get(entry.getKey()));
			arg = theory.not(arg);
			args[i++] = arg;
		}
		// Create the clause.
		final Term base = theory.or(args);

		final HashSet<IndexedPath> paths = info.getPaths();
		final Object[] subannots = new Object[2 * paths.size() + 1];
		int k = 0;
		subannots[k++] = theory.annotatedTerm(CCEquality.QUOTED_CC, diseq);
		for (final IndexedPath p : paths) {
			final CCTerm index = p.getIndex();
			final CCTerm[] path = p.getPath();
			final Term[] subs = new Term[path.length];
			for (int j = 0; j < path.length; ++j) {
				subs[j] = path[j].toSMTTerm(theory);
			}
			if (index == null) {
				subannots[k++] = ":subpath";
				subannots[k++] = subs;
			} else {
				subannots[k++] = ":weakpath";
				subannots[k++] = new Object[] { index.toSMTTerm(theory), subs };
			}
		}
		final Annotation[] annots = new Annotation[] { new Annotation(rule.getKind(), subannots) };
		return theory.term("@lemma", theory.annotatedTerm(annots, base));
	}

	/**
	 * Build the proof term in the form of a resolution step of the main lemma resolved with the auxiliary lemmas in the
	 * order determined by proofOrder.
	 */
	private Term buildProofTerm(final Clause clause, final Theory theory, final ArrayList<ProofInfo> proofOrder) {

		// Store the self-built auxiliary equality literals, such that the
		// arguments of the equality are always in the same order.
		final HashMap<SymmetricPair<CCTerm>, Term> auxLiterals = new HashMap<>();

		// Build all lemma terms.
		final Term[] allLemmas = new Term[proofOrder.size()];
		for (int lemmaNo = 0; lemmaNo < proofOrder.size(); lemmaNo++) {
			// Build the lemma clause.
			final ProofInfo info = proofOrder.get(lemmaNo);
			Term diseq;
			boolean isTrivialDiseq = false;
			if (lemmaNo == 0) { // main lemma
				CCTerm diseqLHS = mAnnot.getDiseq().getFirst();
				CCTerm diseqRHS = mAnnot.getDiseq().getSecond();
				CCEquality diseqAtom = CClosure.createEquality(diseqLHS, diseqRHS);
				if (diseqAtom != null) {
					diseq = diseqAtom.getSMTFormula(theory, false);
				} else {
					diseq = theory.term("=", diseqLHS.toSMTTerm(theory), diseqRHS.toSMTTerm(theory));
					isTrivialDiseq = true;
				}
			} else {
				// auxLiteral should already have been created by the lemma that needs it.
				assert auxLiterals.containsKey(info.getDiseq());
				diseq = auxLiterals.get(info.getDiseq());
			}

			// Build lemma annotations.
			Term lemma = buildLemma(theory, lemmaNo == 0 ? mRule : RuleKind.CC, info, diseq, isTrivialDiseq,
					auxLiterals);
			if (lemmaNo != 0) {
				final Term pivot = theory.annotatedTerm(CCEquality.QUOTED_CC, diseq);
				lemma = theory.annotatedTerm(new Annotation[] { new Annotation(":pivot", pivot) }, lemma);
			}
			allLemmas[lemmaNo] = lemma;
		}
		// If there is at least one auxiliary lemma, return a resolution term
		if (allLemmas.length > 1) {
			return theory.term("@res", allLemmas);
		}
		// Otherwise just return the array lemma
		return allLemmas[0];
	}

	private boolean isEqualityLiteral(final SymmetricPair<CCTerm> termPair) {
		return mEqualityLiterals.containsKey(termPair) && mEqualityLiterals.get(termPair).getSign() < 0;
	}

	private boolean isDisequalityLiteral(final SymmetricPair<CCTerm> termPair) {
		return mEqualityLiterals.containsKey(termPair) && mEqualityLiterals.get(termPair).getSign() > 0;
	}

	private boolean isTrivialDisequality(final SymmetricPair<CCTerm> termPair) {
		final SharedTerm first = termPair.getFirst().getSharedTerm();
		final SharedTerm second = termPair.getSecond().getSharedTerm();
		if (first == null || second == null || first.getOffset() == null || second.getOffset() == null)
			return false;
		if (first.getLinVar() == second.getLinVar() && first.getFactor() == second.getFactor()) {
			return first.getOffset() != second.getOffset();
		}
		MutableAffinTerm sum = new MutableAffinTerm();
		if (first.getLinVar() != null) {
			sum.add(first.getFactor(), first.getLinVar());
		}
		sum.add(first.getOffset());
		if (second.getLinVar() != null) {
			sum.add(second.getFactor().negate(), second.getLinVar());
		}
		sum.add(second.getOffset().negate());
		return sum.isInt() && !sum.getConstant().div(sum.getGCD()).isIntegral();
	}

	private boolean isStoreTerm(CCTerm term) {
		// term == store a i v
		if (term instanceof CCAppTerm) {
			term = ((CCAppTerm) term).getFunc();
			// term == store a i
			if (term instanceof CCAppTerm) {
				term = ((CCAppTerm) term).getFunc();
				// term == store a
				if (term instanceof CCAppTerm) {
					term = ((CCAppTerm) term).getFunc();
					// term == store
					if (term instanceof CCBaseTerm) {
						return ((CCBaseTerm) term).getFunctionSymbol().getName().equals("store");
					}
				}
			}
		}
		return false;
	}

	private boolean isSelectTerm(CCTerm term) {
		// term == select a i
		if (term instanceof CCAppTerm) {
			term = ((CCAppTerm) term).getFunc();
			// term == select a
			if (term instanceof CCAppTerm) {
				term = ((CCAppTerm) term).getFunc();
				// term == select
				if (term instanceof CCBaseTerm) {
					return ((CCBaseTerm) term).getFunctionSymbol().getName().equals("select");
				}
			}
		}
		return false;
	}

	private boolean isConstTerm(CCTerm term) {
		// term == const v
		if (term instanceof CCAppTerm) {
			term = ((CCAppTerm) term).getFunc();
			// term == const
			if (term instanceof CCBaseTerm) {
				return ((CCBaseTerm) term).getFunctionSymbol().getName().equals("const");
			}
		}
		return false;
	}

	/**
	 * Find argument paths for a congruence. These may also be literals from the original clause. Note that a function
	 * can have several arguments, and a path is needed for each of them!
	 *
	 * @return The argument paths, if they exist for all arguments, or null to indicate that the termpair is not a
	 *         congruence.
	 */
	private ProofInfo findCongruencePaths(CCTerm first, CCTerm second) {
		final ProofInfo proofInfo = new ProofInfo();
		proofInfo.mLemmaDiseq = new SymmetricPair<CCTerm>(first, second);
		proofInfo.mProofPaths.add(new IndexedPath(null, new CCTerm[] { first, second }));
		while (first != second) {
			if (!(first instanceof CCAppTerm) || !(second instanceof CCAppTerm)) {
				// This is not a congruence
				return null;
			}
			final CCTerm firstArg = ((CCAppTerm) first).getArg();
			final CCTerm secondArg = ((CCAppTerm) second).getArg();
			final SymmetricPair<CCTerm> argPair = new SymmetricPair<>(firstArg, secondArg);
			if (firstArg != secondArg) {
				proofInfo.mProofPaths.add(new IndexedPath(null, new CCTerm[] { firstArg, secondArg }));
				if (isEqualityLiteral(argPair)) {
					proofInfo.mProofLiterals.put(argPair, mEqualityLiterals.get(argPair));
				} else if (mPathProofMap.containsKey(argPair)) {
					proofInfo.mSubProofs.put(argPair, mPathProofMap.get(argPair));
				} else {
					// If no path was found for the arguments, termPair is not a congruence!
					return null;
				}
			}
			// Continue with the function term. If it is a CCAppTerm itself, this
			// corresponds to a function with several arguments.
			first = ((CCAppTerm) first).getFunc();
			second = ((CCAppTerm) second).getFunc();
		}
		mPathProofMap.put(proofInfo.mLemmaDiseq, proofInfo);
		return proofInfo;
	}

	/**
	 * Search for a select path between two given arrays and paths from the select indices to the weakpath index for
	 * which one wants to prove equality of the array elements.
	 *
	 * @return the select path and (if needed) index paths, or null if there were no suitable paths for the term pair.
	 */
	private SelectEdge findSelectPath(final SymmetricPair<CCTerm> termPair, final CCTerm weakpathindex) {
		// first check for trivial select-const edges, i.e., (const (select a j)) and a with j = weakpathindex.
		if (isConstTerm(termPair.getFirst())) {
			CCTerm value = ArrayTheory.getValueFromConst((CCAppTerm) termPair.getFirst());
			if (isSelect(value, termPair.getSecond(), weakpathindex)) {
				return new SelectEdge(value, value);
			}
		}
		if (isConstTerm(termPair.getSecond())) {
			CCTerm value = ArrayTheory.getValueFromConst((CCAppTerm) termPair.getSecond());
			if (isSelect(value, termPair.getFirst(), weakpathindex)) {
				return new SelectEdge(value, value);
			}
		}


		for (final SymmetricPair<CCTerm> equality : mAllEqualities) {
			// Find some select path.
			final CCTerm start = equality.getFirst();
			final CCTerm end = equality.getSecond();
			if (isGoodSelectStep(start, end, termPair, weakpathindex)) {
				return new SelectEdge(start, end);
			}
			if (isGoodSelectStep(end, start, termPair, weakpathindex)) {
				return new SelectEdge(end, start);
			}
		}
		return null;
	}

	/**
	 * Check if the equality sel1 == sel2 explains the weak step on weakpathindex for termPair.
	 */
	private boolean isGoodSelectStep(CCTerm sel1, CCTerm sel2, SymmetricPair<CCTerm> termPair,
			final CCTerm weakpathindex) {
		return (isSelect(sel1, termPair.getFirst(), weakpathindex) || isConst(termPair.getFirst(), sel1))
				&& (isSelect(sel2, termPair.getSecond(), weakpathindex) || isConst(termPair.getSecond(), sel2));
	}

	/**
	 * Check if select is a select on array on weakpathindex or something equal to weakpathindex.
	 */
	private boolean isSelect(CCTerm select, CCTerm array, final CCTerm weakpathindex) {
		if (!isSelectTerm(select) || ArrayTheory.getArrayFromSelect((CCAppTerm) select) != array)
			return false;
		CCTerm index = ArrayTheory.getIndexFromSelect((CCAppTerm) select);
		return (index == weakpathindex || mAllEqualities.contains(new SymmetricPair<>(weakpathindex, index)));
	}

	/**
	 * Check if array is an application of const on value
	 */
	private boolean isConst(CCTerm array, CCTerm value) {
		return (isConstTerm(array) && ArrayTheory.getValueFromConst((CCAppTerm) array) == value);
	}
}
