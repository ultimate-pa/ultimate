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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CongruencePath.SubPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.WeakCongruencePath.WeakSubPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Annotations for array theory lemmas. A theory lemma is annotated with a set of paths and literals on these paths. A
 * special role plays the diseq literal which occurs positively in the clause. In the negated clause this is the
 * disequality that is in conflict with the other (dis)equalities. For read-over-weakeq lemmas, this is a disequality
 * between array elements, for weakeq-ext lemmas, it is a disequality between arrays. The main path (index 0) starts and
 * ends with one side of the diseq literal for weakeq-ext, and with the select indices for read-over-weakeq. The weak
 * paths ensure equality of the elements of two arrays at the weakpath index (corresponding to a store or select index).
 * Every step must either be explained by a literal from the clause or by a congruence and an auxiliary CC lemma, or, in
 * weak paths, one term is a store "copy" of the other, or a pair of arrays between which there exists a select path as
 * well as paths or equality literals between the path index and the select indices. Congruences in the main and weak
 * paths are outsourced into auxiliary CC lemmas.
 *
 * @author hoenicke, schindler
 */

public class ArrayAnnotation extends CCAnnotation {

	enum RuleKind {
		READ_OVER_WEAKEQ(":read-over-weakeq"), WEAKEQ_EXT(":weakeq-ext");

		String mKind;

		private RuleKind(final String kind) {
			mKind = kind;
		}

		public String getKind() {
			return mKind;
		}
	}

	final CCTerm[] mWeakIndices;
	final RuleKind mRule;
	final IndexedPath[] mIndexedPaths;

	private HashMap<SymmetricPair<CCTerm>, Literal> mEqualityLiterals;
	private HashMap<SymmetricPair<CCTerm>, IndexedPath> mSubPathMap;
	private HashMap<IndexedPath, ProofInfo> mPathProofMap;

	public ArrayAnnotation(final CCEquality diseq, final Collection<SubPath> paths, final RuleKind rule) {
		super(diseq, paths);
		mWeakIndices = new CCTerm[mPaths.length];
		mIndexedPaths = new IndexedPath[mPaths.length];
		int i = 0;
		for (final SubPath p : paths) {
			mWeakIndices[i] = p instanceof WeakSubPath ? ((WeakSubPath) p).getIndex() : null;
			mIndexedPaths[i] = new IndexedPath(mWeakIndices[i], mPaths[i]);
			i++;
		}
		mRule = rule;
	}

	public CCTerm[] getWeakIndices() {
		return mWeakIndices;
	}

	/**
	 * This class is used to keep together paths and their indices (i.e. null for subpaths, and weakpathindex else).
	 */
	class IndexedPath {
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
	}

	/**
	 * This class can be used to store the data needed to prove one path or one disequality, respectively. For a
	 * disequality, the required proof data is: - the proof paths with path indices (index != 0 marks weak paths), in
	 * particular the first subpath and the weakpaths for the main disequality, or the congruence paths for auxiliary CC
	 * lemmas), - equality and disequality literals from the original clause to explain the single steps in these paths,
	 * as well as literals generated in order to outsource congruences, and - the information which sub-proofs are
	 * needed to explain these congruences. For a single path, only the literals and sub-proofs are necessary.
	 */
	private class ProofInfo {

		// Information needed to build the proof graph
		private SymmetricPair<CCTerm> mLemmaDiseq;
		private final HashMap<SymmetricPair<CCTerm>, Literal> mProofLiterals;
		private LinkedHashSet<IndexedPath> mProofPaths;
		private final HashMap<SymmetricPair<CCTerm>, LinkedHashSet<SymmetricPair<CCTerm>>> mSubProofs;

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

		public HashMap<SymmetricPair<CCTerm>, LinkedHashSet<SymmetricPair<CCTerm>>> getSubProofs() {
			return mSubProofs;
		}

		public int getNumParents() {
			return mNumParents;
		}

		public void resetNumParents() {
			mNumParents = 0;
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
		 * Collect the information needed to prove a lemma. For the main lemma paths, pairs of consecutive terms can be
		 * (i) equality literals from the clause (-> are added to proofLiterals), or they are of the form (ii) (a (store
		 * a k v)), (-> nothing to do if it is in the main path of weakeq-ext, for the other weakpaths in weakeq-ext and
		 * weakpaths in read-over-weakeq lemmas a disequality literal showing that the store is at an index different to
		 * weakpathindex is needed), or (iii) ((f a) (f b)), a congruence (-> adds a new literal to the lemma and a new
		 * auxiliary lemma in terms of a subproof), or (iv) (a b), a pair of arrays, and there exists a select path
		 * between them and paths for both select indices to the weakpathindex, if they are not trivially equal or
		 * equality literals from the clause (-> adds new literals for the end terms of the select path and the index
		 * paths (or the corresponding clause literals), and a new auxiliary lemma proving the new select term literal).
		 * These are all possible cases. For the auxiliary CC lemmas, only (i) and (iii) are possible.
		 */
		private void collectProofInfoDiseq(final SymmetricPair<CCTerm> diseq, final LinkedHashSet<IndexedPath> paths) {
			mLemmaDiseq = diseq;
			mProofPaths = paths;
			// Go through all paths needed for this diseq
			for (final IndexedPath indexedPath : paths) {
				final ProofInfo pathInfo = mPathProofMap.get(indexedPath);
				// "Paths" built as a main path of a congruence have no proof info.
				if (pathInfo != null) {
					mProofLiterals.putAll(pathInfo.getLiterals());
					mSubProofs.putAll(pathInfo.getSubProofs());
				}
			}
			mProofLiterals.remove(diseq);
			// Remove self-dependencies
			mSubProofs.remove(diseq);
		}

		/**
		 * Collect the proof info for one path.
		 */
		private void collectProofInfoOnePath(final IndexedPath indexedPath) {
			final CCTerm pathIndex = indexedPath.getIndex();
			final CCTerm[] path = indexedPath.getPath();
			// Check cases (i) - (iv) for all term pairs.
			for (int i = 0; i < path.length - 1; i++) {
				final CCTerm firstTerm = path[i];
				final CCTerm secondTerm = path[i + 1];
				final SymmetricPair<CCTerm> termPair = new SymmetricPair<>(firstTerm, secondTerm);
				// Case (i)
				if (isEqualityLiteral(termPair)) {
					mProofLiterals.put(termPair, mEqualityLiterals.get(termPair));
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
					// In the main path of weakeq-ext, no index disequality is needed
					if (pathIndex == null) {
						continue;
					}
					final CCTerm storeIndex = ArrayTheory.getIndexFromStore((CCAppTerm) storeTerm);
					final SymmetricPair<CCTerm> indexPair = new SymmetricPair<>(pathIndex, storeIndex);
					if (isDisequalityLiteral(indexPair)) {
						mProofLiterals.put(indexPair, mEqualityLiterals.get(indexPair));
						continue;
					}
				}
				// Case (iii)
				final LinkedHashSet<SymmetricPair<CCTerm>> ccArgPaths = findCongruencePaths(firstTerm, secondTerm);
				// If there are paths for all arguments, the term pair is a congruence
				if (ccArgPaths != null) {
					final LinkedHashSet<SymmetricPair<CCTerm>> ccPaths = new LinkedHashSet<>();
					ccPaths.add(termPair); // main path in CC annotation
					ccPaths.addAll(ccArgPaths);
					mProofLiterals.put(termPair, mEqualityLiterals.get(termPair));
					mSubProofs.put(termPair, ccPaths);
					continue;
				}
				// Case (iv)
				final ArrayList<SymmetricPair<CCTerm>> selectAndIndexPaths = findSelectPath(termPair, pathIndex);
				if (selectAndIndexPaths != null) {
					final LinkedHashSet<SymmetricPair<CCTerm>> proofPaths = new LinkedHashSet<>();
					proofPaths.addAll(selectAndIndexPaths);
					final SymmetricPair<CCTerm> selectPath = selectAndIndexPaths.get(0);
					// If the select path is not a clause equality, a subproof is needed.
					if (!isEqualityLiteral(selectPath)) {
						LinkedHashSet<SymmetricPair<CCTerm>> selectPathSingleton =
								new LinkedHashSet<SymmetricPair<CCTerm>>();
						selectPathSingleton.add(selectPath);
						mSubProofs.put(selectPath, selectPathSingleton);
					}
					// If there are index paths, check for congruences and add new subproofs for those.
					if (proofPaths.size() > 1) {
						for (int j = 1; j < proofPaths.size(); j++) {
							final SymmetricPair<CCTerm> indexPair = selectAndIndexPaths.get(j);
							if (!isEqualityLiteral(indexPair)) {
								final LinkedHashSet<SymmetricPair<CCTerm>> argPaths =
										findCongruencePaths(indexPair.getFirst(), indexPair.getSecond());
								if (argPaths != null) {
									final LinkedHashSet<SymmetricPair<CCTerm>> ccPaths = new LinkedHashSet<>();
									ccPaths.add(indexPair);
									ccPaths.addAll(argPaths);
									mSubProofs.put(indexPair, ccPaths);
								}
							}
						}
					}
					// Add literals for all path ends.
					for (final SymmetricPair<CCTerm> proofPath : proofPaths) {
						mProofLiterals.put(proofPath, mEqualityLiterals.get(proofPath));
					}
					continue;
				}
				// If all cases failed, something is seriously wrong.
				throw new IllegalArgumentException("Cannot explain term pair " + termPair.toString());
			}
		}

		/**
		 * Merge the proof info of a congruence lemma into a parent's proof info.
		 */
		private void mergeProofInfo(final ProofInfo otherProof) {
			final SymmetricPair<CCTerm> otherDiseq = otherProof.getDiseq();
			// If the other disequality is not a literal from the main clause,
			// merging corresponds to resolving the parent lemma with the auxiliary lemma
			// and therefore the disequality has to be removed from the lemma clause.
			if (!mEqualityLiterals.containsKey(otherDiseq)) {
				mProofLiterals.remove(otherDiseq);
			}
			// Literals, paths and subproofs are added.
			mProofLiterals.putAll(otherProof.getLiterals());
			// In order to get the correct dependency order, remove the paths
			// needed in the child proof and re-add them at a later position.
			mProofPaths.removeAll(otherProof.getPaths());
			// Only add paths which were not fresh built as main path for the
			// congruence which is merged now
			for (final IndexedPath otherProofPath : otherProof.getPaths()) {
				if (mSubPathMap.containsValue(otherProofPath)) {
					mProofPaths.add(otherProofPath);
				}
			}
			mSubProofs.putAll(otherProof.getSubProofs());
			// Remove the child lemma from subProofs.
			mSubProofs.remove(otherDiseq);
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
	@Override
	public Term toTerm(final Clause clause, final Theory theory) {
		// Store all clause literals
		mEqualityLiterals = collectClauseLiterals(clause);
		// Store all subpaths
		mSubPathMap = makeSubPathMap();
		// For each single path, find the information needed to prove it
		mPathProofMap = makePathProofMap();

		// Collect the paths needed to prove the main disequality
		final SymmetricPair<CCTerm> mainDiseq = new SymmetricPair<>(mDiseq.getLhs(), mDiseq.getRhs());
		final LinkedHashSet<IndexedPath> mainPaths = findMainPaths();

		// Build the proof graph starting with the main disequality.
		// During this process, the required auxiliary lemmas are determined.
		final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph = buildProofGraph(mainDiseq, mainPaths);
		// Determine the order of the auxiliary lemmas in the resolution tree.
		final ArrayList<SymmetricPair<CCTerm>> proofOrder = determineProofOrder(mainDiseq, proofGraph);

		// Build the final proof term
		return buildProofTerm(clause, theory, proofOrder, proofGraph);
	}

	/**
	 * Store all original clause literals as a SymmetricPair for better comparison, mapped to the original literal.
	 */
	private HashMap<SymmetricPair<CCTerm>, Literal> collectClauseLiterals(final Clause clause) {
		final HashMap<SymmetricPair<CCTerm>, Literal> clauseLiterals = new HashMap<>();
		CCTerm lhs, rhs;
		Literal literal;
		CCEquality atom;
		for (int i = 0; i < clause.getSize(); i++) {
			literal = clause.getLiteral(i);
			atom = (CCEquality) literal.getAtom();
			lhs = atom.getLhs();
			rhs = atom.getRhs();
			clauseLiterals.put(new SymmetricPair<>(lhs, rhs), literal);
		}
		return clauseLiterals;
	}

	/**
	 * Build a map from the pairs of subpath ends to the array containing the whole path. This helps to find select and
	 * congruence paths more efficiently by comparing SymmetricPairs.
	 */
	private HashMap<SymmetricPair<CCTerm>, IndexedPath> makeSubPathMap() {
		final HashMap<SymmetricPair<CCTerm>, IndexedPath> pathMap = new HashMap<>();
		for (int i = 0; i < mIndexedPaths.length; i++) {
			final IndexedPath indexedPath = mIndexedPaths[i];
			if (indexedPath.getIndex() == null) {
				final CCTerm[] path = indexedPath.getPath();
				final SymmetricPair<CCTerm> pathEnds = new SymmetricPair<>(path[0], path[path.length - 1]);
				pathMap.put(pathEnds, indexedPath);
			}
		}
		return pathMap;
	}

	/**
	 * Collect the information needed to prove each single path of this lemma.
	 */
	private HashMap<IndexedPath, ProofInfo> makePathProofMap() {
		final HashMap<IndexedPath, ProofInfo> proofMap = new HashMap<>();
		for (int p = 0; p < mIndexedPaths.length; p++) {
			final IndexedPath indexedPath = mIndexedPaths[p];
			final ProofInfo pathInfo = new ProofInfo();
			pathInfo.collectProofInfoOnePath(indexedPath);
			proofMap.put(indexedPath, pathInfo);
		}
		return proofMap;
	}

	/**
	 * Collect all paths needed to prove the main disequality, i.e. the main path which starts with one side of the main
	 * diseq and ends with the other (for weakeq-ext) or which starts with the select index of one side of the main
	 * diseq and ends with the other select index (for read-over-weakeq), and all weakpaths.
	 */
	private LinkedHashSet<IndexedPath> findMainPaths() {
		final LinkedHashSet<IndexedPath> mainPaths = new LinkedHashSet<>();
		IndexedPath firstSubPath = (mIndexedPaths[0].getIndex() == null) ? mIndexedPaths[0] : null;
		if (firstSubPath != null) {
			// for read-over-weakeq, outsource congruences in the index path
			if (mRule.getKind().equals(":read-over-weakeq")) {
				if (firstSubPath.getPath().length > 2) {
					final ProofInfo pathInfo = new ProofInfo();
					pathInfo.collectProofInfoOnePath(firstSubPath);
					IndexedPath newFirstSubPath = new IndexedPath(null, new CCTerm[] { firstSubPath.getPath()[0],
							firstSubPath.getPath()[firstSubPath.getPath().length - 1] });
					mPathProofMap.put(newFirstSubPath, pathInfo);
				}
			}
			mainPaths.add(firstSubPath);
		}
		for (int i = 0; i < mIndexedPaths.length; i++) {
			if (mIndexedPaths[i].getIndex() != null) {
				mainPaths.add(mIndexedPaths[i]);
			}
		}
		return mainPaths;
	}

	/**
	 * Build the proof graph. A node corresponds to either the main array lemma, or an auxiliary lemma explaining
	 * congruences. The children of a node are the subproofs in its proof info. Each congruence in the main lemma
	 * creates a new auxiliary CC lemma. Subordinate congruences are included in their parent lemma unless they are
	 * needed in more than one lemma.
	 */
	private HashMap<SymmetricPair<CCTerm>, ProofInfo> buildProofGraph(final SymmetricPair<CCTerm> mainDiseq,
			final LinkedHashSet<IndexedPath> mainPaths) {

		final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph = new HashMap<>();
		final ArrayDeque<Map.Entry<SymmetricPair<CCTerm>, LinkedHashSet<SymmetricPair<CCTerm>>>> todoBuild =
				new ArrayDeque<>();

		final ProofInfo mainInfo = new ProofInfo();
		mainInfo.collectProofInfoDiseq(mainDiseq, mainPaths);
		proofGraph.put(mainDiseq, mainInfo);
		if (!mainInfo.getSubProofs().isEmpty()) {
			todoBuild.addAll(mainInfo.getSubProofs().entrySet());
		}

		// Find subproof information.
		while (!(todoBuild.isEmpty())) {
			final Map.Entry<SymmetricPair<CCTerm>, LinkedHashSet<SymmetricPair<CCTerm>>> auxLemma =
					todoBuild.removeLast();
			final SymmetricPair<CCTerm> auxDiseq = auxLemma.getKey();

			// Don't build a lemma for congruences explained by a literal!
			if (isEqualityLiteral(auxDiseq)) {
				continue;
			}
			// Collect the proof info for this auxiliary lemma if it has not
			// been collected before.
			if (!(proofGraph.containsKey(auxDiseq))) {
				final LinkedHashSet<IndexedPath> paths = new LinkedHashSet<>();
				for (final SymmetricPair<CCTerm> auxLemmaPath : auxLemma.getValue()) {
					// Get the complete paths
					if (mSubPathMap.containsKey(auxLemmaPath)) {
						paths.add(mSubPathMap.get(auxLemmaPath));
					}
					// or if the main path of a congruence does not yet exist,
					// build it from the lhs and rhs of this congruence.
					else {
						final CCTerm[] auxLemmaPathArray = new CCTerm[2];
						auxLemmaPathArray[0] = auxLemmaPath.getFirst();
						auxLemmaPathArray[1] = auxLemmaPath.getSecond();
						paths.add(new IndexedPath(null, auxLemmaPathArray));
					}
				}
				final ProofInfo proofInfo = new ProofInfo();
				proofInfo.collectProofInfoDiseq(auxDiseq, paths);
				proofGraph.put(auxDiseq, proofInfo);
				// Add any subproofs to the todo stack
				if (!(proofInfo.getSubProofs().isEmpty())) {
					todoBuild.addAll(proofInfo.getSubProofs().entrySet());
				}
			}
		}

		// Determine the number of parents for each node
		determineAllNumParents(proofGraph);
		// Merge nodes with only one parent (other than mainDiseq) into the
		// parent node in order to avoid unnecessary splitting of the proof.
		mergeSingleDependencies(proofGraph, mainDiseq);
		// Adjust the number of parents.
		determineAllNumParents(proofGraph);

		return proofGraph;
	}

	/**
	 * Set mNumParents in the proof info for all nodes of a given proof graph.
	 */
	private void determineAllNumParents(final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph) {
		// First, reset mNumParents for each node.
		for (final Map.Entry<SymmetricPair<CCTerm>, ProofInfo> proofNode : proofGraph.entrySet()) {
			proofNode.getValue().resetNumParents();
		}
		// Now count the parents.
		for (final Map.Entry<SymmetricPair<CCTerm>, ProofInfo> proofNode : proofGraph.entrySet()) {
			final ProofInfo proofInfo = proofNode.getValue();
			for (final SymmetricPair<CCTerm> child : proofInfo.mSubProofs.keySet()) {
				proofGraph.get(child).increaseNumParents();
			}
		}
	}

	/**
	 * Merge nodes with only one parent (other than mainDiseq) into this parent node. Note that the parent numbers in
	 * the proof info may need updates!
	 */
	private void mergeSingleDependencies(final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph,
			final SymmetricPair<CCTerm> mainDiseq) {
		final ArrayDeque<SymmetricPair<CCTerm>> todoMerge = new ArrayDeque<>();
		if (!proofGraph.get(mainDiseq).getSubProofs().isEmpty()) {
			todoMerge.addAll(proofGraph.get(mainDiseq).getSubProofs().keySet());
		}
		while (!todoMerge.isEmpty()) {
			boolean merge = false;
			final SymmetricPair<CCTerm> parentNode = todoMerge.removeFirst();
			if (proofGraph.get(parentNode).getSubProofs().isEmpty()) {
				continue;
			}

			final Set<SymmetricPair<CCTerm>> children = new HashSet<>();
			children.addAll(proofGraph.get(parentNode).getSubProofs().keySet());
			for (final SymmetricPair<CCTerm> childNode : children) {
				if ((proofGraph.get(childNode).getNumParents() == 1) && (!parentNode.equals(mainDiseq))) {
					if (!proofGraph.get(childNode).getSubProofs().isEmpty()) {
						merge = true;
					}
					proofGraph.get(parentNode).mergeProofInfo(proofGraph.get(childNode));
					proofGraph.remove(childNode);
				}
			}

			// If at least one child was merged and has children itself,
			// review the parent node for new merging possibilities.
			if (merge) {
				todoMerge.add(parentNode);
				determineAllNumParents(proofGraph);
			}
			// Otherwise, continue with the children.
			else {
				todoMerge.addAll(proofGraph.get(parentNode).getSubProofs().keySet());
			}
		}
	}

	/**
	 * Determine the order of the resolution tree. Start with the main lemma, represented by the main disequality, and
	 * continue with its successor nodes. A node representing an auxiliary lemma can appear in the proof order only
	 * after all its parent nodes.
	 */
	private ArrayList<SymmetricPair<CCTerm>> determineProofOrder(final SymmetricPair<CCTerm> mainDiseq,
			final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph) {
		final ArrayList<SymmetricPair<CCTerm>> proofOrder = new ArrayList<>();
		final ArrayDeque<SymmetricPair<CCTerm>> todo = new ArrayDeque<>();
		todo.add(mainDiseq);
		while (!todo.isEmpty()) {
			final SymmetricPair<CCTerm> node = todo.removeFirst();
			final ProofInfo nodeInfo = proofGraph.get(node);
			proofOrder.add(node);
			if (!nodeInfo.getSubProofs().isEmpty()) {
				for (final SymmetricPair<CCTerm> child : nodeInfo.getSubProofs().keySet()) {
					proofGraph.get(child).increaseVisitedParentsCounter();
					if (proofGraph.get(child).haveVisitedAllParents()) {
						if (!todo.contains(child)) {
							todo.add(child);
						}
					}
				}
			}
		}
		return proofOrder;
	}

	/**
	 * Build the proof term in the form of a resolution step of the main lemma resolved with the auxiliary lemmas in the
	 * order determined by proofOrder.
	 */
	private Term buildProofTerm(final Clause clause, final Theory theory,
			final ArrayList<SymmetricPair<CCTerm>> proofOrder,
			final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph) {

		// Store the self-built auxiliary equality literals, such that the
		// arguments of the equality are always in the same order.
		final HashMap<SymmetricPair<CCTerm>, Term> auxLiterals = new HashMap<>();

		// Build all lemma terms.
		final Term[] allLemmas = new Term[proofOrder.size()];
		for (int lemmaNo = 0; lemmaNo < proofOrder.size(); lemmaNo++) {
			// Build the lemma clause.
			final ProofInfo info = proofGraph.get(proofOrder.get(lemmaNo));
			Term diseq;
			if (lemmaNo == 0) { // main lemma
				diseq = mDiseq.getSMTFormula(theory);
			} else if (auxLiterals.containsKey(info.getDiseq())) {
				diseq = auxLiterals.get(info.getDiseq());
			} else {
				final SymmetricPair<CCTerm> diseqPair = info.getDiseq();
				diseq = Coercion.buildEq(diseqPair.getFirst().toSMTTerm(theory),
						diseqPair.getSecond().toSMTTerm(theory));
				auxLiterals.put(diseqPair, diseq);
			}
			// Collect the new clause literals.
			final Term[] args = new Term[info.getLiterals().size() + 1];
			final Annotation[] quote = new Annotation[] { new Annotation(":quoted", null) };
			int i = 0;
			// First the (positive) diseq literal
			args[i++] = theory.annotatedTerm(quote, diseq);
			// then the other literals, there may also be other positive literals.
			for (final Map.Entry<SymmetricPair<CCTerm>, Literal> entry : info.getLiterals().entrySet()) {
				Term arg = null;
				if (entry.getValue() != null) { // original clause literals
					arg = entry.getValue().getAtom().getSMTFormula(theory);
					arg = theory.annotatedTerm(quote, arg);
					if (entry.getValue().getSign() < 0) {
						arg = theory.not(arg);
					}
				} else { // new literals built when outsourcing congruences (always negated)
					if (auxLiterals.containsKey(entry.getKey())) {
						arg = theory.annotatedTerm(quote, auxLiterals.get(entry.getKey()));
						arg = theory.not(arg);
					} else {
						final Term lhs = entry.getKey().getFirst().toSMTTerm(theory);
						final Term rhs = entry.getKey().getSecond().toSMTTerm(theory);
						arg = Coercion.buildEq(lhs, rhs);
						auxLiterals.put(entry.getKey(), arg);
						arg = theory.annotatedTerm(quote, arg);
						arg = theory.not(arg);
					}
				}
				args[i++] = arg;
			}
			// Create the clause.
			final Term base = theory.or(args);

			// Build lemma annotations.
			String rule;
			if (lemmaNo == 0) {
				rule = mRule.getKind();
			} else {
				rule = ":CC";
			}
			final HashSet<IndexedPath> paths = info.getPaths();
			final Object[] subannots = new Object[2 * paths.size() + 1];
			int k = 0;
			subannots[k++] = diseq;
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
			final Annotation[] annots = new Annotation[] { new Annotation(rule, subannots) };
			Term lemma = theory.term("@lemma", theory.annotatedTerm(annots, base));
			if (lemmaNo != 0) {
				final Term pivot = theory.annotatedTerm(quote, diseq);
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
		if (mEqualityLiterals.containsKey(termPair)) {
			if (mEqualityLiterals.get(termPair).getSign() < 0) {
				return true;
			}
		}
		return false;
	}

	private boolean isDisequalityLiteral(final SymmetricPair<CCTerm> termPair) {
		if (mEqualityLiterals.containsKey(termPair)) {
			if (mEqualityLiterals.get(termPair).getSign() > 0) {
				return true;
			}
		}
		return false;
	}

	private boolean isStoreTerm(final CCTerm term) {
		if (term instanceof CCAppTerm) {
			if (((CCAppTerm) term).getFunc() instanceof CCAppTerm) {
				if (((CCAppTerm) ((CCAppTerm) term).getFunc()).getFunc() instanceof CCAppTerm) {
					if (((CCAppTerm) ((CCAppTerm) ((CCAppTerm) term).getFunc()).getFunc()).getFunc().toString()
							.contains("store")) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private boolean isSelectTerm(final CCTerm term) {
		if (term instanceof CCAppTerm) {
			if (((CCAppTerm) term).getFunc() instanceof CCAppTerm) {
				if (((CCAppTerm) ((CCAppTerm) term).getFunc()).getFunc().toString().contains("select")) {
					return true;
				}
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
	private LinkedHashSet<SymmetricPair<CCTerm>> findCongruencePaths(final CCTerm firstTerm, final CCTerm secondTerm) {
		final LinkedHashSet<SymmetricPair<CCTerm>> ccPaths = new LinkedHashSet<>();
		if (!(firstTerm instanceof CCAppTerm && secondTerm instanceof CCAppTerm)) {
			// Test. this happens if we outsource congruences from the indexpath in read-ocver-weakeq
			final SymmetricPair<CCTerm> termPair = new SymmetricPair<>(firstTerm, secondTerm);
			if (mSubPathMap.containsKey(termPair)) {
				ccPaths.add(termPair);
				return ccPaths;
			}
			//
			return null;
		}
		CCTerm first = firstTerm;
		CCTerm second = secondTerm;
		while (first instanceof CCAppTerm && second instanceof CCAppTerm) {
			final CCTerm firstArg = ((CCAppTerm) first).getArg();
			final CCTerm secondArg = ((CCAppTerm) second).getArg();
			final SymmetricPair<CCTerm> argPair = new SymmetricPair<>(firstArg, secondArg);
			boolean existsArgPath = false;
			if (firstArg == secondArg) {
				existsArgPath = true;
			} else if (isEqualityLiteral(argPair)) {
				existsArgPath = true;
				ccPaths.add(argPair);
			} else if (mSubPathMap.containsKey(argPair)) {
				existsArgPath = true;
				ccPaths.add(argPair);
			}
			// If no path was found for the arguments, termPair is not a congruence!
			if (!existsArgPath) {
				return null;
			}
			// Continue with the function term. If it is a CCAppTerm itself, this
			// corresponds to a function with several arguments.
			first = ((CCAppTerm) first).getFunc();
			second = ((CCAppTerm) second).getFunc();
		}
		return ccPaths;
	}

	/**
	 * Search for a select path between two given arrays and paths from the select indices to the weakpath index for
	 * which one wants to prove equality of the array elements.
	 *
	 * @return the select path and (if needed) index paths, or null if there were no suitable paths for the term pair.
	 */
	private ArrayList<SymmetricPair<CCTerm>> findSelectPath(final SymmetricPair<CCTerm> termPair,
			final CCTerm weakpathindex) {
		final ArrayList<SymmetricPair<CCTerm>> selectAndIndexPaths = new ArrayList<>();
		for (final SymmetricPair<CCTerm> tryPath : mSubPathMap.keySet()) {
			boolean needFirstIndexPath = true;
			boolean needSecondIndexPath = true;
			SymmetricPair<CCTerm> firstIndexPath = null;
			SymmetricPair<CCTerm> secondIndexPath = null;
			// Find some select path.
			final CCTerm start = tryPath.getFirst();
			final CCTerm end = tryPath.getSecond();
			if (!(isSelectTerm(start) && isSelectTerm(end))) {
				continue;
			}
			// Check if the arrays of the select terms match the term pair.
			final CCTerm startArray = ArrayTheory.getArrayFromSelect((CCAppTerm) start);
			final CCTerm endArray = ArrayTheory.getArrayFromSelect((CCAppTerm) end);
			final SymmetricPair<CCTerm> arrayPair = new SymmetricPair<>(startArray, endArray);
			if (!(termPair.equals(arrayPair))) {
				continue;
			}
			// Check if the select indices equal the weakpath index.
			final CCTerm startIndex = ArrayTheory.getIndexFromSelect((CCAppTerm) start);
			final CCTerm endIndex = ArrayTheory.getIndexFromSelect((CCAppTerm) end);
			// If the select indices equal weakpath index, there's nothing to do.
			if (startIndex == weakpathindex) {
				needFirstIndexPath = false;
			}
			if (endIndex == weakpathindex) {
				needSecondIndexPath = false;
			}
			// Otherwise, we need equality literals or paths between the select
			// indices and the weakpath index.
			final SymmetricPair<CCTerm> firstIndexPair = new SymmetricPair<>(weakpathindex, startIndex);
			final SymmetricPair<CCTerm> secondIndexPair = new SymmetricPair<>(weakpathindex, endIndex);
			if (needFirstIndexPath) {
				if (isEqualityLiteral(firstIndexPair)) {
					firstIndexPath = firstIndexPair;
					needFirstIndexPath = false;
				} else if (mSubPathMap.containsKey(firstIndexPair)) {
					firstIndexPath = firstIndexPair;
					needFirstIndexPath = false;
				}
			}
			if (needSecondIndexPath) {
				if (isEqualityLiteral(secondIndexPair)) {
					secondIndexPath = secondIndexPair;
					needSecondIndexPath = false;
				} else if (mSubPathMap.containsKey(secondIndexPair)) {
					secondIndexPath = secondIndexPair;
					needSecondIndexPath = false;
				}
			}
			// If a select path and corresponding index paths (if needed) were
			// found, return them.
			if (!needFirstIndexPath && !needSecondIndexPath) {
				selectAndIndexPaths.add(tryPath);
				if (firstIndexPath != null) {
					selectAndIndexPaths.add(firstIndexPath);
				}
				if (secondIndexPath != null) {
					selectAndIndexPaths.add(secondIndexPath);
				}
				return selectAndIndexPaths;
			}
			// If there were no suitable index paths, try a new path.
		}
		// If no select paths could be found, return null.
		return null;
	}
}
