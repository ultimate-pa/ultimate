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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;
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
					collectEquality(new SymmetricPair<>(pathIndex, index));
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
					if (isTrivialDisequality(indexPair)) {
						continue;
					}
				}
				// Case (iv) select
				if (mRule == RuleKind.WEAKEQ_EXT && pathIndex != null) {
					final SymmetricPair<CCTerm> selectEq = findSelectPath(termPair, pathIndex);
					if (selectEq != null) {
						// TODO: decide should we add a trivial strong path for select equalities?
						final IndexedPath selectPath =
								new IndexedPath(null, new CCTerm[] { selectEq.getFirst(), selectEq.getSecond() });
						collectStrongPath(selectPath);
						collectSelectIndexEquality(selectEq.getFirst(), pathIndex);
						collectSelectIndexEquality(selectEq.getSecond(), pathIndex);
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
	final ArrayAnnotation.RuleKind mRule;
	final IndexedPath[] mIndexedPaths;

	private HashMap<SymmetricPair<CCTerm>, Literal> mEqualityLiterals;
	private HashMap<SymmetricPair<CCTerm>, ProofInfo> mPathProofMap;
	private HashSet<SymmetricPair<CCTerm>> mAllEqualities;

	public CCProofGenerator(final ArrayAnnotation arrayAnnot) {
		mAnnot = arrayAnnot;
		mRule = arrayAnnot.mRule;
		mIndexedPaths = new IndexedPath[arrayAnnot.mPaths.length];
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
		// Store all clause literals
		collectClauseLiterals(clause);
		// Create a proof info for each sub path that isn't an asserted equality.
		collectStrongEqualities();
		mAllEqualities = new HashSet<>();
		mAllEqualities.addAll(mPathProofMap.keySet());
		for (final Map.Entry<SymmetricPair<CCTerm>, Literal> equalityEntry : mEqualityLiterals.entrySet()) {
			if (equalityEntry.getValue().getSign() < 0) {
				mAllEqualities.add(equalityEntry.getKey());
			}
		}

		// Collect the paths needed to prove the main disequality
		final SymmetricPair<CCTerm> mainDiseq = new SymmetricPair<>(mAnnot.mDiseq.getLhs(), mAnnot.mDiseq.getRhs());
		final ProofInfo mainInfo = findMainPaths();
		mainInfo.mLemmaDiseq = mainDiseq;
		mPathProofMap.put(mainDiseq, mainInfo);

		// Build the proof graph starting with the main disequality.
		// During this process, the required auxiliary lemmas are determined.
		final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph = buildProofGraph(mainInfo);
		// Determine the order of the auxiliary lemmas in the resolution tree.
		final ArrayList<ProofInfo> proofOrder = determineProofOrder(mainInfo);

		// Build the final proof term
		return buildProofTerm(clause, theory, proofOrder, proofGraph);
	}

	/**
	 * Store all original clause literals as a SymmetricPair for better comparison, mapped to the original literal.
	 */
	private void collectClauseLiterals(final Clause clause) {
		mEqualityLiterals = new HashMap<>();
		CCTerm lhs, rhs;
		Literal literal;
		CCEquality atom;
		for (int i = 0; i < clause.getSize(); i++) {
			literal = clause.getLiteral(i);
			atom = (CCEquality) literal.getAtom();
			lhs = atom.getLhs();
			rhs = atom.getRhs();
			mEqualityLiterals.put(new SymmetricPair<>(lhs, rhs), literal);
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
				if (!isEqualityLiteral(pathEnds) || mPathProofMap.containsKey(pathEnds)) {
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
		case WEAKEQ_EXT:
			assert mIndexedPaths[0].getIndex() == null;
			mainProof.collectWeakPath(mIndexedPaths[0]);
			break;
		case READ_OVER_WEAKEQ: {
			IndexedPath firstPath = mIndexedPaths[0];
			if (firstPath.getIndex() == null) {
				// for read-over-weakeq, create a short first path
				final CCTerm[] path = firstPath.getPath();
				final SymmetricPair<CCTerm> indexPair = new SymmetricPair<CCTerm>(path[0], path[path.length - 1]);
				mainProof.collectEquality(indexPair);
				if (path.length > 2) {
					firstPath = new IndexedPath(null, new CCTerm[] { path[0], path[path.length - 1] });
				}
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
	 * Build the proof graph. A node corresponds to either the main array lemma, or an auxiliary lemma explaining
	 * congruences. The children of a node are the subproofs in its proof info. Each congruence in the main lemma
	 * creates a new auxiliary CC lemma. Subordinate congruences are included in their parent lemma unless they are
	 * needed in more than one lemma.
	 */
	private HashMap<SymmetricPair<CCTerm>, ProofInfo> buildProofGraph(final ProofInfo mainInfo) {

		// Determine the number of parents for each node
		// determineAllNumParents(mPathProofMap);
		// Merge nodes with only one parent (other than mainDiseq) into the
		// parent node in order to avoid unnecessary splitting of the proof.
		// mergeSingleDependencies(mPathProofMap, mainInfo.mLemmaDiseq);
		// Adjust the number of parents.
		determineAllNumParents(mainInfo);
		return mPathProofMap;
	}

	/**
	 * Set mNumParents in the proof info for all nodes of a given proof graph.
	 */
	private void determineAllNumParents(final ProofInfo mainInfo) {
		// First, reset mNumParents for each node.
		for (final ProofInfo proofNode : mPathProofMap.values()) {
			proofNode.resetNumParents();
		}
		// Now count the parents.
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

	/**
	 * Build the proof term in the form of a resolution step of the main lemma resolved with the auxiliary lemmas in the
	 * order determined by proofOrder.
	 */
	private Term buildProofTerm(final Clause clause, final Theory theory, final ArrayList<ProofInfo> proofOrder,
			final HashMap<SymmetricPair<CCTerm>, ProofInfo> proofGraph) {

		// Store the self-built auxiliary equality literals, such that the
		// arguments of the equality are always in the same order.
		final HashMap<SymmetricPair<CCTerm>, Term> auxLiterals = new HashMap<>();

		// Build all lemma terms.
		final Term[] allLemmas = new Term[proofOrder.size()];
		for (int lemmaNo = 0; lemmaNo < proofOrder.size(); lemmaNo++) {
			// Build the lemma clause.
			final ProofInfo info = proofOrder.get(lemmaNo);
			Term diseq;
			if (lemmaNo == 0) { // main lemma
				diseq = mAnnot.mDiseq.getSMTFormula(theory);
			} else {
				// auxLiteral should already have been created by the lemma that needs it.
				assert auxLiterals.containsKey(info.getDiseq());
				diseq = auxLiterals.get(info.getDiseq());
			}
			// Collect the new clause literals.
			final Term[] args = new Term[info.getLiterals().size() + 1 + info.getSubProofs().size()];
			final Annotation[] quote = new Annotation[] { new Annotation(":quotedCC", null) };
			int i = 0;
			// First the (positive) diseq literal
			args[i++] = theory.annotatedTerm(quote, diseq);
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
					auxLiterals.put(entry.getKey(), Coercion.buildEq(lhs, rhs));
				}
				/* these are always negated equalities */
				Term arg = theory.annotatedTerm(quote, auxLiterals.get(entry.getKey()));
				arg = theory.not(arg);
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
			subannots[k++] = theory.annotatedTerm(quote, diseq);
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
	private SymmetricPair<CCTerm> findSelectPath(final SymmetricPair<CCTerm> termPair, final CCTerm weakpathindex) {
		for (final SymmetricPair<CCTerm> equality : mAllEqualities) {
			// Find some select path.
			final CCTerm start = equality.getFirst();
			final CCTerm end = equality.getSecond();
			if (isGoodSelectStep(start, end, termPair, weakpathindex)
					|| isGoodSelectStep(end, start, termPair, weakpathindex)) {
				return equality;
			}
		}
		return null;
	}

	/**
	 * Check if the equality sel1 == sel2 explains the weak step on weakpathindex for termPair.
	 */
	private boolean isGoodSelectStep(CCTerm sel1, CCTerm sel2, SymmetricPair<CCTerm> termPair, final CCTerm weakpathindex) {
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
