/*
 * Copyright (C) 2014 University of Freiburg
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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory.ArrayNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Class to compute weak congruence paths and the extended select over store lemmas.
 *
 * @author Jochen Hoenicke
 */
public class WeakCongruencePath extends CongruencePath {

	/**
	 * A simple cursor to iterate simultaneously through the array nodes and the ccterms.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class Cursor {
		public CCTerm mTerm;
		public ArrayNode mArrayNode;

		public Cursor(CCTerm term, ArrayNode arrayNode) {
			mTerm = term;
			mArrayNode = arrayNode;
		}

		public void update(CCTerm term, ArrayNode arrayNode) {
			mTerm = term;
			mArrayNode = arrayNode;
		}
	}

	static class WeakSubPath extends SubPath {
		private final CCTerm mIdx;
		private final CCTerm mIdxRep;

		public WeakSubPath(CCTerm idx, CCTerm start, boolean produceProofs) {
			super(start, produceProofs);
			mIdx = idx;
			mIdxRep = idx.getRepresentative();
		}

		@Override
		public String toString() {
			return "Weakpath " + mIdx
				+ (mTermsOnPath == null ? "" : " " + mTermsOnPath.toString());
		}

		public CCTerm getIndex() {
			return mIdx;
		}
	}

	final ArrayTheory mArrayTheory;

	public WeakCongruencePath(ArrayTheory arrayTheory) {
		super(arrayTheory.getCClosure());
		mArrayTheory = arrayTheory;
	}

	public Clause computeSelectOverWeakEQ(CCAppTerm select1, CCAppTerm select2,
			boolean produceProofs) {
		final CCTerm i1 = select1.getArg();
		final CCTerm i2 = select2.getArg();
		final CCTerm a = ((CCAppTerm) select1.getFunc()).getArg();
		final CCTerm b = ((CCAppTerm) select2.getFunc()).getArg();
		final SubPath indexPath = computePath(i1, i2);
		final WeakSubPath weakPath =
				computeWeakPath(a, b, i1, produceProofs);
		mAllPaths.addFirst(weakPath);
		if (indexPath != null) {
			mAllPaths.addFirst(indexPath);
		}

		return generateClause(new SymmetricPair<CCTerm>(select1, select2), produceProofs, RuleKind.READ_OVER_WEAKEQ);
	}

	public Clause computeSelectConstOverWeakEQ(CCAppTerm select1, CCAppTerm const2, boolean produceProofs) {
		final CCTerm value2 = const2.getArg();

		final CCTerm i1 = select1.getArg();
		final CCTerm a = ((CCAppTerm) select1.getFunc()).getArg();
		final WeakSubPath weakPath = computeWeakPath(a, const2, i1, produceProofs);
		mAllPaths.addFirst(weakPath);
		return generateClause(new SymmetricPair<CCTerm>(select1, value2), produceProofs, RuleKind.READ_CONST_WEAKEQ);
	}

	public Clause computeConstOverWeakEQ(CCAppTerm const1, CCAppTerm const2, boolean produceProofs) {
		final CCTerm value1 = const1.getArg();
		final CCTerm value2 = const2.getArg();

		final HashSet<CCTerm> storeIndices = new HashSet<CCTerm>();
		final Cursor start = new Cursor(const1, mArrayTheory.mCongRoots.get(const1.getRepresentative()));
		final Cursor dest = new Cursor(const2, mArrayTheory.mCongRoots.get(const2.getRepresentative()));
		final SubPath path = collectPathPrimary(start, dest, storeIndices, produceProofs);
		mAllPaths.addFirst(path);
		return generateClause(new SymmetricPair<CCTerm>(value1, value2), produceProofs, RuleKind.CONST_WEAKEQ);
	}

	/**
	 * Compute the clause and proof for a weakeq-ext lemma.
	 *
	 * The caller must ensure that the array node for the const term is already the weak representative.
	 * 
	 * @param a
	 *            The first array
	 * @param b
	 *            The second array.
	 * @param produceProofs
	 *            true, if proof should be produced.
	 * @return the clause, optionally annotated with a proof.
	 */
	public Clause computeWeakeqExt(CCTerm a, CCTerm b, boolean produceProofs) {
		assert a != b;
		final HashSet<CCTerm> storeIndices = new HashSet<CCTerm>();
		final Cursor start = new Cursor(a, mArrayTheory.mCongRoots.get(a.getRepresentative()));
		final Cursor dest = new Cursor(b, mArrayTheory.mCongRoots.get(b.getRepresentative()));
		final SubPath path = collectPathPrimary(start, dest, storeIndices, produceProofs);
		for (final CCTerm idx : storeIndices) {
			final WeakSubPath weakpath = computeWeakCongruencePath(a, b, idx, produceProofs);
			mAllPaths.addFirst(weakpath);
		}
		mAllPaths.addFirst(path);
		return generateClause(new SymmetricPair<CCTerm>(a, b), produceProofs, RuleKind.WEAKEQ_EXT);
	}

	/**
	 * Compute a weak equivalence path and the corresponding weak path condition. The path conditions and disequalities
	 * are added to the set of literals mAllEqualities and to mAllPaths.
	 *
	 * @param array1
	 *            Start of the path.
	 * @param array2
	 *            End of the path.
	 * @param index
	 *            Index for this path.
	 * @param produceProofs
	 *            Proof production enabled?
	 * @return Path information for this weak path.
	 */
	private WeakSubPath computeWeakPath(CCTerm array1, CCTerm array2, CCTerm index, boolean produceProofs) {

		final HashSet<CCTerm> storeIndices = new HashSet<CCTerm>();
		final CCTerm indexRep = index.getRepresentative();
		final Cursor cursor1 = new Cursor(array1, mArrayTheory.mCongRoots.get(array1.getRepresentative()));
		final Cursor cursor2 = new Cursor(array2, mArrayTheory.mCongRoots.get(array2.getRepresentative()));
		final WeakSubPath sub1 = new WeakSubPath(index, array1, produceProofs);
		final WeakSubPath sub2 = new WeakSubPath(index, array2, produceProofs);
		assert cursor1.mArrayNode.getWeakIRepresentative(indexRep)
				== cursor2.mArrayNode.getWeakIRepresentative(indexRep);
		int count1 = cursor1.mArrayNode.countSecondaryEdges(indexRep);
		int count2 = cursor2.mArrayNode.countSecondaryEdges(indexRep);
		while (count1 > count2) {
			collectPathOneSecondary(cursor1, sub1, storeIndices, produceProofs);
			count1--;
		}
		while (count2 > count1) {
			collectPathOneSecondary(cursor2, sub2, storeIndices, produceProofs);
			count2--;
		}
		while (cursor1.mArrayNode.findSecondaryNode(indexRep) != cursor2.mArrayNode.findSecondaryNode(indexRep)) {
			collectPathOneSecondary(cursor1, sub1, storeIndices, produceProofs);
			collectPathOneSecondary(cursor2, sub2, storeIndices, produceProofs);
		}
		sub1.addSubPath(collectPathPrimary(cursor1, cursor2, storeIndices, produceProofs));
		sub1.addSubPath(sub2);
		for (final CCTerm storeIdx : storeIndices) {
			computeIndexDiseq(index, storeIdx);
		}
		return sub1;
	}

	/**
	 * Compute a weak congruence path and the corresponding path condition. The path conditions are added to the set of
	 * literals constituting the conflict.
	 *
	 * @param array1
	 *            Start of the path.
	 * @param array2
	 *            End of the path.
	 * @param index
	 *            Index for this path.
	 * @param produceProofs
	 *            Proof production enabled?
	 * @return Path information for this weak path. Other paths are added as side-effect to mAllPaths.
	 */
	private WeakSubPath computeWeakCongruencePath(CCTerm array1, CCTerm array2, CCTerm index, boolean produceProofs) {

		final CCTerm indexRep = index.getRepresentative();
		final ArrayNode node1 = mArrayTheory.mCongRoots.get(array1.getRepresentative());
		final ArrayNode node2 = mArrayTheory.mCongRoots.get(array2.getRepresentative());
		final ArrayNode rep1 = node1.getWeakIRepresentative(indexRep);
		final ArrayNode rep2 = node2.getWeakIRepresentative(indexRep);
		if (rep1 == rep2) {
			return computeWeakPath(array1, array2, index, produceProofs);
		}
		WeakSubPath path;
		CCTerm select1, select2;
		// compute weak path from array1 to left-hand-side of select edge
		if (rep1.mConstTerm != null) {
			// const array on left-hand-side
			path = computeWeakPath(array1, rep1.mConstTerm, index, produceProofs);
			select1 = ArrayTheory.getValueFromConst(rep1.mConstTerm);
		} else {
			// get select for left-hand-side
			CCAppTerm select = rep1.mSelects.get(indexRep);
			CCTerm selectArray = ArrayTheory.getArrayFromSelect(select);
			SubPath indexPath = computePath(index, ArrayTheory.getIndexFromSelect(select));
			if (indexPath != null) {
				mAllPaths.addFirst(indexPath);
			}
			path = computeWeakPath(array1, selectArray, index, produceProofs);
			select1 = select;
		}
		// compute weak path from right-hand-side of select edge to array2
		if (rep2.mConstTerm != null) {
			// const array on right-hand-side
			path.addEntry(rep2.mConstTerm, null);
			path.addSubPath(computeWeakPath(rep2.mConstTerm, array2, index, produceProofs));
			select2 = ArrayTheory.getValueFromConst(rep2.mConstTerm);
		} else {
			// get select for right-hand-side
			CCAppTerm select = rep2.mSelects.get(indexRep);
			CCTerm selectArray = ArrayTheory.getArrayFromSelect(select);
			SubPath indexPath = computePath(index, ArrayTheory.getIndexFromSelect(select));
			if (indexPath != null) {
				mAllPaths.addFirst(indexPath);
			}
			path.addEntry(selectArray, null);
			path.addSubPath(computeWeakPath(selectArray, array2, index, produceProofs));
			select2 = select;
		}
		// compute the path between the selects or between select and constant value.
		assert select1.getRepresentative() == select2.getRepresentative();
		// check for trivial select edge (select-const).
		if (select1 != select2) {
			mAllPaths.addFirst(computePath(select1, select2));
		}
		return path;
	}

	public void collectPathOnePrimary(Cursor cursor, SubPath path, HashSet<CCTerm> storeIndices) {
		final ArrayNode node = cursor.mArrayNode;
		final CCAppTerm store = node.mPrimaryStore;
		CCTerm t1 = store;
		CCTerm t2 = ArrayTheory.getArrayFromStore(store);
		if (t2.mRepStar == cursor.mArrayNode.mTerm) {
			final CCTerm t = t2;
			t2 = t1;
			t1 = t;
		}
		assert t1.mRepStar == node.mTerm;
		assert t2.mRepStar == node.mPrimaryEdge.mTerm;
		path.addSubPath(computePath(cursor.mTerm, t1));
		path.addEntry(t2, null);
		cursor.update(t2, node.mPrimaryEdge);
		storeIndices.add(ArrayTheory.getIndexFromStore(store));
	}

	/**
	 * Connect two arrays using only store edges on the path.  It adds the 
	 * path from start to the dest and moves the cursor accordingly. 
	 * @param start the starting array and array node.
	 * @param dest the destination array and array node.
	 * @param storeIndices accumulates the store indices on the path.
	 * @param produceProofs true, if path must be recorded.
	 * @returns the path connecting the arrays.
	 */
	private SubPath collectPathPrimary(Cursor start, Cursor dest, HashSet<CCTerm> storeIndices,
			boolean produceProofs) {
		final SubPath path1 = new SubPath(start.mTerm, produceProofs);
		final SubPath path2 = new SubPath(dest.mTerm, produceProofs);
		int count1 = start.mArrayNode.countPrimaryEdges();
		int count2 = dest.mArrayNode.countPrimaryEdges();
		while (count1 > count2) {
			collectPathOnePrimary(start, path1, storeIndices);
			count1--;
		}
		while (count2 > count1) {
			collectPathOnePrimary(dest, path2, storeIndices);
			count2--;
		}
		while (start.mArrayNode != dest.mArrayNode) {
			collectPathOnePrimary(start, path1, storeIndices);
			collectPathOnePrimary(dest, path2, storeIndices);
		}
		path1.addSubPath(computePath(start.mTerm, dest.mTerm));
		path1.addSubPath(path2);
		return path1;
	}

	/**
	 * Step over a single secondary edge in the weak-i equivalence class. This assumes there is such a secondary edge.
	 * It adds the path from cursor to the destination of the secondary edge and moves the cursor accordingly.
	 * 
	 * @param cursor
	 *            The position where the path currently ends. This is updated to the destination of the secondary edge.
	 * @param path
	 *            the accumulated path that is extended at the end.
	 * @param storeIndices
	 *            accumulates the store indices on the path.
	 * @param produceProofs
	 *            true, if path must be recorded.
	 */
	private void collectPathOneSecondary(Cursor cursor, WeakSubPath path, HashSet<CCTerm> storeIndices,
			boolean produceProofs) {
		final ArrayNode selector = cursor.mArrayNode.findSecondaryNode(path.mIdxRep);
		final CCAppTerm store = selector.mSecondaryStore;
		CCTerm t1 = store;
		CCTerm t2 = ArrayTheory.getArrayFromStore(store);
		ArrayNode n1 = mArrayTheory.mCongRoots.get(t1.mRepStar);
		ArrayNode n2 = mArrayTheory.mCongRoots.get(t2.mRepStar);
		if (n2.findSecondaryNode(path.mIdxRep) == selector) {
			//swap nodes, such that n1 is in the same region as node.
			final ArrayNode n = n2;
			n2 = n1;
			n1 = n;
			final CCTerm t = t2;
			t2 = t1;
			t1 = t;
		}
		assert (n1.findSecondaryNode(path.mIdxRep) == selector);
		path.addSubPath(collectPathPrimary(cursor, new Cursor(t1, n1), 
				storeIndices, produceProofs));
		path.addEntry(t2, null);
		cursor.update(t2, n2);
		storeIndices.add(ArrayTheory.getIndexFromStore(store));
	}

	/**
	 * Compute a justification for the disequality of two indices.
	 * @param idx          The index for a weak equality path.
	 * @param idxFromStore The index of an edge in the weakeq graph.
	 */
	private void computeIndexDiseq(CCTerm idx, CCTerm idxFromStore) {
		final CCEquality eqlit = CClosure.createEquality(idx, idxFromStore);
		if (eqlit != null) {
			mAllLiterals.add(eqlit.negate());
		}
	}

	private Clause generateClause(SymmetricPair<CCTerm> diseq, boolean produceProofs, RuleKind rule) {
		if (diseq != null) {
			final CCEquality eq = CClosure.createEquality(diseq.getFirst(), diseq.getSecond());
			if (eq != null) {
				// Note that it can actually happen that diseq is already in
				// the list of all literals (because it is an index assumption).
				mAllLiterals.add(eq.negate());
			}
		}

		final Literal[] lemma = new Literal[mAllLiterals.size()];
		int i = 0;
		for (final Literal l: mAllLiterals) {
			lemma[i++] = l.negate();
		}
		final Clause c = new Clause(lemma);
		if (produceProofs) {
			c.setProof(new LeafNode(
					LeafNode.THEORY_ARRAY, createAnnotation(diseq, rule)));
		}
		return c;
	}

	private CCAnnotation createAnnotation(SymmetricPair<CCTerm> diseq, RuleKind rule) {
		return new CCAnnotation(diseq, mAllPaths, rule);
	}
}
