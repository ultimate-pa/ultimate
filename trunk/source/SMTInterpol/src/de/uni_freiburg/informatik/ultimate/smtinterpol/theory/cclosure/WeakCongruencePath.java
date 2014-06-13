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

import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory.ArrayNode;

/**
 * Class to compute weak congruence paths and the extended select over
 * store lemmata.
 * 
 * @author hoenicke
 */
public class WeakCongruencePath extends CongruencePath {
	
	/**
	 * A simple cursor to iterate simultaneously through the
	 * array nodes and the ccterms.
	 * 
	 * @author hoenicke
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
	
	class WeakSubPath extends SubPath {
		private final CCTerm mIdx;
		private final CCTerm mIdxRep;
		
		public WeakSubPath(CCTerm idx, CCTerm start, boolean produceProofs) {
			super(start, produceProofs);
			mIdx = idx;
			mIdxRep = idx.getRepresentative();
		}
		
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

	private CCEquality createEquality(CCTerm t1, CCTerm t2) {
		EqualityProxy ep = t1.getFlatTerm().createEquality(t2.getFlatTerm());
		if (ep == EqualityProxy.getFalseProxy())
				return null;
		Literal res = ep.getLiteral();
		if (res instanceof CCEquality)
			return (CCEquality) res;
		return ep.createCCEquality(t1.getFlatTerm(), t2.getFlatTerm());
	}
	
	public Clause computeSelectOverWeakEQ(CCAppTerm select1, CCAppTerm select2,
			boolean produceProofs) {
		CCEquality eq = createEquality(select1, select2);

		CCTerm i1 = select1.getArg();
		CCTerm i2 = select2.getArg();
		CCTerm a = ((CCAppTerm) select1.getFunc()).getArg();
		CCTerm b = ((CCAppTerm) select2.getFunc()).getArg();
		SubPath indexPath = computePath(i1, i2);
		WeakSubPath weakPath =
				computeWeakPath(a, b, i1, produceProofs);
		mAllPaths.addFirst(weakPath);
		if (indexPath != null)
			mAllPaths.addFirst(indexPath);

		return generateClause(eq, produceProofs, RuleKind.READ_OVER_WEAKEQ);
	}
	
	public Clause computeWeakeqExt(CCTerm a, CCTerm b, boolean produceProofs) {
		assert a != b;
		CCEquality eq = createEquality(a, b);
		HashSet<CCTerm> storeIndices = new HashSet<CCTerm>();
		Cursor start = new Cursor(a, 
				mArrayTheory.mCongRoots.get(a.getRepresentative()));
		Cursor dest = new Cursor(b, 
				mArrayTheory.mCongRoots.get(b.getRepresentative()));
		SubPath path = collectPathNoSelect(start, dest, storeIndices, produceProofs);
		for (CCTerm idx : storeIndices) {
			WeakSubPath weakpath = 
					computeWeakPathWithModulo(a, b, idx, produceProofs);
			mAllPaths.addFirst(weakpath);
		}
		mAllPaths.addFirst(path);
		return generateClause(eq, produceProofs, RuleKind.WEAKEQ_EXT);
	}

	/**
	 * Compute a weak path and the corresponding weak path condition.  The path
	 * condition is added to the set of literals constituting the conflict.
	 * @param a              Start of the path.
	 * @param b              End of the path.
	 * @param idx            Index for this path.
	 * @param weakeq         Weak equivalence relation.
	 * @param produceProofs  Proof production enabled?
	 * @return Path information for this weak path.
	 */
	private WeakSubPath computeWeakPath(CCTerm ccArray1, CCTerm ccArray2, 
			CCTerm index, boolean produceProofs) {

		HashSet<CCTerm> storeIndices = new HashSet<CCTerm>();
		CCTerm indexRep = index.getRepresentative();
		Cursor cursor1 = new Cursor(ccArray1, 
				mArrayTheory.mCongRoots.get(ccArray1.getRepresentative())); 
		Cursor cursor2 = new Cursor(ccArray2, 
				mArrayTheory.mCongRoots.get(ccArray2.getRepresentative())); 
		WeakSubPath sub1 = new WeakSubPath(index, ccArray1, produceProofs);
		WeakSubPath sub2 = new WeakSubPath(index, ccArray2, produceProofs);
		assert cursor1.mArrayNode.getWeakIRepresentative(indexRep)
				== cursor2.mArrayNode.getWeakIRepresentative(indexRep);
		int count1 = cursor1.mArrayNode.countSelectEdges(indexRep);
		int count2 = cursor2.mArrayNode.countSelectEdges(indexRep);
		while (count1 > count2) {
			collectPathOneSelect(cursor1, sub1, storeIndices, produceProofs);
			count1--;
		}
		while (count2 > count1) {
			collectPathOneSelect(cursor2, sub2, storeIndices, produceProofs);
			count2--;
		}
		while (cursor1.mArrayNode.findSelectNode(indexRep)
				!= cursor2.mArrayNode.findSelectNode(indexRep)) {
			collectPathOneSelect(cursor1, sub1, storeIndices, produceProofs);
			collectPathOneSelect(cursor2, sub2, storeIndices, produceProofs);
		}
		sub1.addSubPath(
			collectPathNoSelect(cursor1, cursor2, storeIndices, produceProofs));
		sub1.addSubPath(sub2);
		for (CCTerm storeIdx : storeIndices) {
			computeIndexDiseq(index, storeIdx);
		}
		return sub1;
	}
	
	/**
	 * Compute a weak path and the corresponding weak path condition.  The path
	 * condition is added to the set of literals constituting the conflict.
	 * @param a              Start of the path.
	 * @param b              End of the path.
	 * @param idx            Index for this path.
	 * @param weakeq         Weak equivalence relation.
	 * @param useModuloEdges Use edges induced by equalities on values stored at
	 *                       <code>idx</code>.
	 * @param produceProofs  Proof production enabled?
	 * @return Path information for this weak path.
	 */
	private WeakSubPath computeWeakPathWithModulo(CCTerm array1, CCTerm array2, 
			CCTerm index, boolean produceProofs) {

		CCTerm indexRep = index.getRepresentative();
		ArrayNode node1 = mArrayTheory.mCongRoots.get(array1.getRepresentative()); 
		ArrayNode node2 = mArrayTheory.mCongRoots.get(array2.getRepresentative()); 
		ArrayNode rep1 = node1.getWeakIRepresentative(indexRep);
		ArrayNode rep2 = node2.getWeakIRepresentative(indexRep);
		if (rep1 == rep2)
			return computeWeakPath(array1, array2, index, produceProofs);
		CCAppTerm select1 = rep1.mSelects.get(indexRep);
		CCAppTerm select2 = rep2.mSelects.get(indexRep);
		assert select1.getRepresentative() == select2.getRepresentative();
		// match select indices with index. 
		SubPath indexPath;
		indexPath = computePath(index, ArrayTheory.getIndexFromSelect(select1));
		if (indexPath != null)
			mAllPaths.addFirst(indexPath);
		indexPath = computePath(index, ArrayTheory.getIndexFromSelect(select2));
		if (indexPath != null)
			mAllPaths.addFirst(indexPath);
		// compute the path between the selects.
		mAllPaths.addFirst(computePath(select1, select2));

		// go from ccArrays to select arrays
		CCTerm selArray1 = ArrayTheory.getArrayFromSelect(select1);
		CCTerm selArray2 = ArrayTheory.getArrayFromSelect(select2);
		WeakSubPath weakpath =
				computeWeakPath(array1, selArray1, index, produceProofs);
		weakpath.addEntry(selArray2, null);
		weakpath.addSubPath(
				computeWeakPath(array2, selArray2, index, produceProofs));
		return weakpath;
	}

	
	public void collectPathOneStore(Cursor cursor, SubPath path, 
			HashSet<CCTerm> storeIndices) {
		ArrayNode node = cursor.mArrayNode;
		CCAppTerm store = node.mStoreReason;
		CCTerm t1 = store;
		CCTerm t2 = ArrayTheory.getArrayFromStore(store);
		if (t2.mRepStar == cursor.mArrayNode.mTerm) {
			CCTerm t = t2;
			t2 = t1;
			t1 = t;
		}
		assert t1.mRepStar == node.mTerm;
		assert t2.mRepStar == node.mStoreEdge.mTerm;
		path.addSubPath(computePath(cursor.mTerm, t1));
		path.addEntry(t2, null);
		cursor.update(t2, node.mStoreEdge);
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
	private SubPath collectPathNoSelect(Cursor start, Cursor dest, 
			HashSet<CCTerm> storeIndices, boolean produceProofs) {
		SubPath path1 = new SubPath(start.mTerm, produceProofs);
		SubPath path2 = new SubPath(dest.mTerm, produceProofs);
		int count1 = start.mArrayNode.countStoreEdges();
		int count2 = dest.mArrayNode.countStoreEdges();
		while (count1 > count2) {
			collectPathOneStore(start, path1, storeIndices);
			count1--;
		}
		while (count2 > count1) {
			collectPathOneStore(dest, path2, storeIndices);
			count2--;
		}
		while (start.mArrayNode != dest.mArrayNode) {
			collectPathOneStore(start, path1, storeIndices);
			collectPathOneStore(dest, path2, storeIndices);
		}
		path1.addSubPath(computePath(start.mTerm, dest.mTerm));
		path1.addSubPath(path2);
		return path1;
	}

	/**
	 * Step over a single select edge in the weak-i equivalence class.  This
	 * assumes there is such a select edge.  It adds the path from cursor
	 * to the destination of the select edge and moves the cursor accordingly. 
	 * @param cursor  The position where the path currently ends. This is 
	 * updated to the destination of the select edge
	 * @param path the accumulated path that is extended at the end.
	 * @param storeIndices accumulates the store indices on the path.
	 * @param produceProofs true, if path must be recorded.
	 */
	private void collectPathOneSelect(Cursor cursor, WeakSubPath path,
			HashSet<CCTerm> storeIndices, boolean produceProofs) {
		ArrayNode selector = cursor.mArrayNode.findSelectNode(path.mIdxRep);
		CCAppTerm store = selector.mSelectReason;
		CCTerm t1 = store;
		CCTerm t2 = ArrayTheory.getArrayFromStore(store);
		ArrayNode n1 = mArrayTheory.mCongRoots.get(t1.mRepStar);
		ArrayNode n2 = mArrayTheory.mCongRoots.get(t2.mRepStar);
		if (n2.findSelectNode(path.mIdxRep) == selector) {
			//swap nodes, such that n1 is in the same region as node.
			ArrayNode n = n2;
			n2 = n1;
			n1 = n;
			CCTerm t = t2;
			t2 = t1;
			t1 = t;
		}
		assert (n1.findSelectNode(path.mIdxRep) == selector);
		path.addSubPath(collectPathNoSelect(cursor, new Cursor(t1, n1), 
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
		CCEquality eqlit = createEquality(idx, idxFromStore);
		if (eqlit != null) {
			mAllLiterals.add(eqlit.negate());
		}
	}

	private Clause generateClause(CCEquality diseq, boolean produceProofs,
			RuleKind rule) {
		assert diseq != null;
		// Note that it can actually happen that diseq is already in
		// the list of all literals (because it is an index assumption).
		mAllLiterals.add(diseq.negate());

		Literal[] lemma = new Literal[mAllLiterals.size()];
		int i = 0;
		for (Literal l: mAllLiterals) {
			lemma[i++] = l.negate();
		}
		Clause c = new Clause(lemma);
		if (produceProofs)
			c.setProof(new LeafNode(
					LeafNode.THEORY_ARRAY, createAnnotation(diseq, rule)));
		return c;
	}
	
	private ArrayAnnotation createAnnotation(CCEquality diseq, RuleKind rule) {
		return new ArrayAnnotation(diseq, mAllPaths, rule);
	}
}
