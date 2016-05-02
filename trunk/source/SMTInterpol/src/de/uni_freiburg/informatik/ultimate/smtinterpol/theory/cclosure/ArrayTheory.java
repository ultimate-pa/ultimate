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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArrayValue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

/**
 * Array theory solver based on weak equivalence classes.  The underlying
 * data structure is explained in our paper "Weakly Equivalent Arrays".
 *
 * <p>The function <code>checkpoint</code> computes the weak equivalent graph
 * and collects the equalities that would appear in the weak lemmas, i.e.,
 * the index disequalities and the propagated equality on the select terms.
 * If there is only one equality in a lemma it propagates the lemma.
 * Otherwise, the mere creation of the equality literals, will force the
 * DPLL engine at some point to decide these literals.</p>
 *
 * <p>The produced lemmas will always contain the equalities in a canonical
 * form, namely the propagated equality is on the select terms, for which the
 * equality was propagated and the index disequality is on the index of the
 * first select term with the index of the store term.</p>
 *
 * @author Jochen Hoenicke
 */
public class ArrayTheory implements ITheory {

	/**
	 * <p>The core data structure used by the array theory solver.  For every
	 * strong term equivalence class of an array sort, we create an ArrayNode
	 * representing this array.  The ArrayNodes are connected by store edges,
	 * which form a spanning tree of the weak equivalence class pointing to
	 * the weak representative.  The store edges always combine the ArrayNode
	 * representing the store with the ArrayNode representing the array of the
	 * store.  The direction of the edge may be inverted, though.</p>
	 * 
	 * <p>
	 * In addition there are so called select edges that are induced by another
	 * store (mSelectReason) on a different index than the store that induces
	 * the store edge.  For a given index, the weak equivalence graph would
	 * fall into some smaller equivalence classes, if the store edges with 
	 * that index are removed.  The roots of the smaller equivalence classes
	 * are the original root and the array nodes whose mStoreEdge is on the 
	 * index.  We now combine these smaller equivalence classes by adding
	 * select edges from the root of one small equivalence class to an 
	 * arbitrary node in the other equivalence class, building a new weak-i
	 * equivalence class, which is a subclass of the original one.  The original
	 * root is also a weak-i equivalence root for every index, but there may
	 * be others that are characterized by mSelectEdge being null.
	 * The store and array of the selectReason are guaranteed to be reachable
	 * from the origin and destination of the select edge by using only store
	 * edges on a different index.
	 * </p>
	 * 
	 * <p>The store and select edges induce for every index and every pair
	 * of arrays in the same weak-i equivalence class for that index a 
	 * unique path that connects the arrays only by stores on a different
	 * index.</p>
	 * 
	 * <p>For every index, you have three finer and finer equivalence classes
	 * that together form up the weak-i equivalence class for that index.  The
	 * finest is the strong equivalence class on equalities, represented by
	 * the ccterm data structure.  The next is the indexed weak equivalence 
	 * class induced by the storeEdges if you remove all the stores on that 
	 * index. The store edges combine the ccterms and it is guaranteed that 
	 * their endpoints lie in the ccterm equivalence class they combine.  These 
	 * indexed weak equivalence classes are then combined by the select edges.
	 * Again the endpoints of the select edge lie in the same underlying 
	 * equivalence class in this case the indexed weak equivalence class.</p>
	 * 
	 * @author hoenicke
	 *
	 */
	static class ArrayNode {
		/**
		 * The ccterm this node corresponds to. 
		 * This is always the representative, i.e.,
		 * <code>mTerm.repStar = mTerm</code>.
		 */
		CCTerm mTerm;
		
		/**
		 * The destination node of the store edge.
		 */
		ArrayNode mStoreEdge;
		
		/**
		 * The store corresponding to the store edge.
		 * This must be either an element of mTerm.mMembers or
		 * of mStoreEdge.mTerm.mMembers.  Also this must be a
		 * CCAppTerm of a store.
		 */
		CCAppTerm mStoreReason;
		
		/**
		 * The alternative edge pointing towards the representative in the
		 * weak-i equivalence group, where <code>i</code> is the index
		 * of mStoreTerm.  The mSelectEdges may also form a tree, where the
		 * root is the representative and the arrows point towards the root
		 * node. This must always be a member of the weak-equivalence group.
		 * 
		 * This is null for the weak representative (mStoreEdge == null).
		 */
		ArrayNode mSelectEdge;
		
		/**
		 * The reason for the select edge.  This is either null, if the select
		 * edge was caused by an equality in the outside, or it is a store 
		 * on a different index.
		 */
		CCAppTerm mSelectReason;
		
		/**
		 * The array nodes in the same weak equivalence class form a cyclic 
		 * linked list by virtue of this pointer.
		 */
		ArrayNode mNext;
		
		/**
		 * A map from index to the selects that exists for this weak-i 
		 * equivalence class.  Used to quickly merge weak-i classes and to
		 * quickly compute new equivalences.
		 * We only have to remember one of the select terms, since the
		 * other are supposed to be equal.
		 * 
		 * The key is always the representative of the index of the 
		 * corresponding select.
		 * 
		 * This is an arbitrary map for weak representative (mStoreEdge==null),
		 * should be a singleton for weak-i representatives 
		 * (mSelectEdge == null && mStoreEdge != null) and empty for all
		 * other nodes (mSelectEdge != null)
		 */
		Map<CCTerm, CCAppTerm> mSelects;
		
		/**
		 * Create a new array term corresponding to a ccterm.
		 * @param ccterm the corresponding ccterm.  This must be its own
		 * representative.
		 */
		public ArrayNode(CCTerm ccterm) {
			assert ccterm.isRepresentative();
			mTerm = ccterm;
			mNext = this;
			mStoreEdge = mSelectEdge = null;
			mStoreReason = null;
		}

		/**
		 * Get the representative of the weak equivalence class.  This
		 * is the root of the tree formed by mStoreEdge.
		 * @return the representative array node.
		 */
		public ArrayNode getWeakRepresentative() {
			ArrayNode node = this;
			while (node.mStoreEdge != null)
				node = node.mStoreEdge;
			return node;
		}
		
		/**
		 * Get the representative of the weak-i equivalence class.  This
		 * is an ArrayNode that yields the same value for a select on the
		 * given index.
		 * @param index the index i for which determines the weak-i 
		 *        equivalence class.
		 * @return the representative array node.
		 */
		public ArrayNode getWeakIRepresentative(CCTerm index) {
			index = index.getRepresentative();
			ArrayNode node = this;
			while (node.mStoreEdge != null) {
				if (getIndexFromStore(node.mStoreReason)
						.getRepresentative() == index) {
					if (node.mSelectEdge == null)
						break;
					node = node.mSelectEdge;
				} else {
					node = node.mStoreEdge;
				}
			}
			return node;
		}
		
		/** 
		 * Make this node its weak-i representative, by inverting all 
		 * select edges pointing outwards.  This assumes, that the node
		 * is a weak-i representative, that is not the weak representative,
		 * and that the weak representative is not in the same weak-i
		 * equivalence class, i.e., the outward pointing edges do not point
		 * to the weak representative. 
		 */
		public void invertSelectEdges() {
			assert mStoreEdge != null;
			assert mSelectEdge != null;
			CCTerm index = getIndexFromStore(mStoreReason).getRepresentative();
			assert getWeakIRepresentative(index) != getWeakRepresentative();
			ArrayNode prev = this;
			ArrayNode next = prev.mSelectEdge;
			CCAppTerm prevReason = prev.mSelectReason;
			while (next != null) {
				// first follow the store edges until we find a good store.
				next = next.findSelectNode(index);
				
				// now copy the new edge information
				ArrayNode nextEdge = next.mSelectEdge;
				CCAppTerm nextReason = next.mSelectReason;
				// invert the previous edge
				next.mSelectEdge = prev;
				next.mSelectReason = prevReason;
				// continue inverting
				prev = next;
				prevReason = nextReason;
				next = nextEdge;
			}
			mSelectEdge = null;
			mSelectReason = null;
			mSelects = prev.mSelects;
			prev.mSelects = Collections.emptyMap();
		}
		
		/**
		 * Make this array node the representative of its weak equivalence
		 * group by inverting all the store edges.
		 */
		public void makeWeakRepresentative() {
			if (mStoreEdge == null)
				return;
			HashMap<CCTerm,ArrayNode> seenStores = 
					new HashMap<CCTerm, ArrayNode>();
			HashMap<CCTerm,ArrayNode> todoSelects = 
					new HashMap<CCTerm, ArrayNode>();
			HashMap<CCTerm,CCAppTerm> todoReasons = 
					new HashMap<CCTerm, CCAppTerm>();
			HashMap<CCTerm,CCAppTerm> newSelectMap = 
					new HashMap<CCTerm, CCAppTerm>();
			ArrayNode node = this;
			ArrayNode prev = null;
			CCAppTerm prevStore = null;
			while (node.mStoreEdge != null) {
				ArrayNode next = node.mStoreEdge;
				CCAppTerm nextStore = node.mStoreReason;
				node.mStoreEdge = prev;
				node.mStoreReason = prevStore;
				
				CCTerm index = getIndexFromStore(nextStore).getRepresentative();
				ArrayNode old = seenStores.put(index, next);
				if (old == node) {
					// the node is in the middle of two stores on the same
					// index.  There is no need to move the select-information
					// around.
					//
					// This branch is intentionally left empty!
				} else if (node.mSelectEdge != null) { //NOPMD
					if (old == null) {
						// we have to invert the select edge in the end, but
						// we should wait until the inversion of the store edges
						// is completed.
						todoSelects.put(index, node.mSelectEdge);
						todoReasons.put(index, node.mSelectReason);
					} else {
						// insert the select edge into old node.
						assert (getIndexFromStore(old.mStoreReason)
								.getRepresentative() == index);
						assert (old.mSelectEdge == null);
						old.mSelectEdge = node.mSelectEdge;
						old.mSelectReason = node.mSelectReason;
					}
					node.mSelectEdge = null;
					node.mSelectReason = null;
				} else if (!node.mSelects.isEmpty()) {
					// we need to move the select information.
					if (old == null) {
						assert node.mSelects.get(index) != null;
						newSelectMap.put(index, node.mSelects.get(index)); 
					} else {
						// old is the new weak i representative
						old.mSelects = node.mSelects;
					}
					node.mSelects = Collections.emptyMap();
				}

				prev = node;
				node = next;
				prevStore = nextStore;
			}
			node.mStoreEdge = prev;
			node.mStoreReason = prevStore;
			Map<CCTerm, CCAppTerm> rootSelects = node.mSelects;
			node.mSelects = Collections.emptyMap();
			for (Entry<CCTerm, ArrayNode> entry : seenStores.entrySet()) {
				// The seen stores get the new representatives of their weak-i
				// equivalence groups
				CCTerm index = entry.getKey();
				CCAppTerm select = rootSelects.remove(index);
				if (select != null) {
					entry.getValue().mSelects = 
						Collections.singletonMap(index, select);
				}
			}
			for (Entry<CCTerm, ArrayNode> entry: todoSelects.entrySet()) {
				CCTerm index = entry.getKey();
				ArrayNode dest = entry.getValue();
				dest = dest.findSelectNode(index);
				if (dest.mSelectEdge != null)
					dest.invertSelectEdges();
				dest.mSelectEdge = this;
				dest.mSelectReason = todoReasons.get(index);
				newSelectMap.putAll(dest.mSelects);
				dest.mSelects = Collections.emptyMap();
			}
			newSelectMap.putAll(rootSelects);
			this.mSelects = newSelectMap;
		}

		public void mergeWith(ArrayNode storeNode, CCAppTerm store,
				Set<SymmetricPair<CCAppTerm>> propEqualities) {
			assert getWeakRepresentative() != storeNode.getWeakRepresentative();
			mStoreEdge = storeNode;
			mStoreReason = store;
			
			// merge next linkage
			ArrayNode next = mNext;
			mNext = storeNode.mNext;
			storeNode.mNext = next;
			
			// merge the selects;
			Map<CCTerm, CCAppTerm> newSelects = Collections.emptyMap();
			for (Entry<CCTerm, CCAppTerm> entry : mSelects.entrySet()) {
				CCTerm index = entry.getKey();
				CCAppTerm select = entry.getValue();
				assert select != null;
				if (index == getIndexFromStore(store).getRepresentative()) {
					newSelects = Collections.singletonMap(index, select);
				} else {
					CCAppTerm otherSelect = storeNode.mSelects.get(index);
					if (otherSelect == null) {
						// move the select to new representative.
						storeNode.mSelects.put(index, select);
					} else {
						if (select.getRepresentative() 
								!= otherSelect.getRepresentative()) {
							// add propagated equality
							propEqualities.add(new SymmetricPair<CCAppTerm>(
									select, otherSelect));
						}
					}
				}
			}
			mSelects = newSelects;
		}
		
		public void computeSelects(int mSelectFunNum) {
			mSelects = new HashMap<CCTerm, CCAppTerm>();
			CCParentInfo info = 
					mTerm.mCCPars.getExistingParentInfo(mSelectFunNum);
			if (info != null) {
				for (CCAppTerm.Parent pa : info.mCCParents) {
					CCParentInfo selectas = pa.getData().getRepresentative()
							.mCCPars.getExistingParentInfo(0);
					for (CCAppTerm.Parent spa : selectas.mCCParents) {
						CCAppTerm select = spa.getData();
						assert (getArrayFromSelect(select).getRepresentative() 
								== mTerm);
						assert (select != null);
						mSelects.put(select.mArg.getRepresentative(), select);
					}
				}
			}
		}

		public void mergeSelect(ArrayNode storeNode, CCAppTerm store,
				Set<SymmetricPair<CCAppTerm>> propEqualities) {
			assert storeNode.mStoreEdge == null;
			assert mStoreEdge != null;
			assert getIndexFromStore(mStoreReason).getRepresentative()
					!= getIndexFromStore(store).getRepresentative();
			if (mSelectEdge != null)
				invertSelectEdges();
			mSelectEdge = storeNode;
			mSelectReason = store;
			if (!mSelects.isEmpty()) {
				CCTerm storeIndex
					= getIndexFromStore(mStoreReason).getRepresentative();
				CCAppTerm select = mSelects.get(storeIndex);
				assert (select != null);
				CCAppTerm otherSelect = storeNode.mSelects.get(storeIndex);
				if (otherSelect == null) {
					storeNode.mSelects.put(storeIndex, select);
				} else {
					if (select.getRepresentative()
							!= otherSelect.getRepresentative()) {
						propEqualities.add(new SymmetricPair<CCAppTerm>(
								select, otherSelect));
					}
				}
				mSelects = Collections.emptyMap();
			}
		}

		public int countSelectEdges(CCTerm index) {
			assert index.isRepresentative();
			int count = 0;
			ArrayNode node = this;
			while (node.mStoreEdge != null) {
				if (getIndexFromStore(node.mStoreReason).getRepresentative()
						== index) {
					if (node.mSelectEdge == null)
						break;
					node = node.mSelectEdge;
					count++;
				} else {
					node = node.mStoreEdge;
				}
			}
			return count;
		}

		public ArrayNode findSelectNode(CCTerm index) {
			assert index.isRepresentative();
			ArrayNode node = this;
			while (node.mStoreEdge != null
					&& getIndexFromStore(node.mStoreReason).getRepresentative() 
					!= index) {
				node = node.mStoreEdge;
			}
			return node;
		}

		public int countStoreEdges() {
			int count = 0;
			ArrayNode node = this;
			while (node.mStoreEdge != null) {
				node = node.mStoreEdge;
				count++;
			}
			return count;
		}
		
		/**
		 * Returns the hash code.  This equals the hash code of the underlying
		 * ccterm.  Note that our algorithm guarantees that there is at most
		 * one ArrayTerm created for any ccterm.
		 */
		public int hashCode() {
			return mTerm.hashCode();
		}
		
		public String toString() {
			return "ArrayNode[" + mTerm + "]";
		}
	}
	
	private static class ArrayLemma {
		Set<CCEquality> mUndecidedLits;
		SymmetricPair<CCAppTerm> mPropagatedEq;
		
		public String toString() {
			return "ArrayLemma["+mPropagatedEq+" ; "+ mUndecidedLits +"]";
		}
	}

	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	
	private final int mSelectFunNum;
	
	private final ScopedArrayList<CCTerm> mArrays =
			new ScopedArrayList<CCTerm>();
	private final ScopedHashSet<CCAppTerm> mStores =
			new ScopedHashSet<CCAppTerm>();
	private final ScopedHashSet<CCAppTerm> mDiffs =
			new ScopedHashSet<CCAppTerm>();
	
	private final ArrayDeque<ArrayLemma> mPropClauses = 
			new ArrayDeque<ArrayLemma>();
	
	private final Logger mLogger;
	
	/// Cache for the congruence roots;
	Map<CCTerm,ArrayNode> mCongRoots = null;
	Map<ArrayNode, Map<CCTerm,Object>> mArrayModels = null;
	
	// =============== STATISTICS ===============
	private int mNumInstsSelect = 0;
	private int mNumInstsEq = 0;
	private int mNumBuildWeakEQ = 0;
	private int mNumAddStores = 0;
	private int mNumMerges = 0;
	private int mNumModuloEdges = 0;
	private long mTimeBuildWeakEq = 0;
	private long mTimeBuildWeakEqi = 0;
	private long mTimePropagation = 0;
	private long mTimeExplanations = 0;
	
	private int mNumArrays = 0;
	
	public ArrayTheory(Clausifier clausifier, CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mCClosure.initArrays();
		mSelectFunNum = mCClosure.getSelectNum();
		mLogger = mCClosure.mEngine.getLogger();
	}
	
	@Override
	public Clause startCheck() {
		cleanCaches();
		return null;
	}

	@Override
	public void endCheck() {
		// Don't clean the caches here.  We might need them to build a model!
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if (literal instanceof CCEquality) {
			cleanCaches();
		} else {
			for (ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.remove(literal.negate())
					&& lemma.mUndecidedLits.isEmpty()) {
					return explainPropagation(lemma.mPropagatedEq);
				}
			}
		}
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		cleanCaches();
	}

	@Override
	public Clause checkpoint() {
		if (mCongRoots == null
			&& buildWeakEq()) {
			for (ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.isEmpty())
					return explainPropagation(lemma.mPropagatedEq);
			}
		}
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		Clause conflict = checkpoint();
		if (conflict != null)
			return conflict;
		if (mPropClauses.isEmpty()) {
			boolean foundLemma = computeWeakeqExt();
			if (foundLemma)
				mArrayModels = null;
			else
				mCongRoots = null;
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		long start = System.nanoTime();
		for (ArrayLemma lemma : mPropClauses) {
			if (lemma.mUndecidedLits.size() == 1) {
				if (mLogger.isDebugEnabled())
					mLogger.debug("AL prop: " + lemma);
				Literal lit = lemma.mUndecidedLits.iterator().next();
				mTimePropagation += System.nanoTime() - start;
				lit.getAtom().mExplanation = explainPropagation(lemma.mPropagatedEq);
				return lit;
			}
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		assert literal instanceof CCEquality;
		if (mCongRoots == null)
			buildWeakEq();
		for (ArrayLemma lemma : mPropClauses) {
			Set<CCEquality> lits = lemma.mUndecidedLits;
			if (lits.isEmpty()
				|| (lits.size() == 1 && lits.contains(literal))) {
				return explainPropagation(lemma.mPropagatedEq);
			}
		}
		throw new AssertionError("Cannot explain unit literal!");
	}

	private Clause explainPropagation(SymmetricPair<CCAppTerm> equality) {
		long start = System.nanoTime();
		mNumInstsSelect++;
		WeakCongruencePath path = new WeakCongruencePath(this);
		Clause lemma = path.computeSelectOverWeakEQ(
				equality.getFirst(), equality.getSecond(),
				mCClosure.mEngine.isProofGenerationEnabled());
		if (mLogger.isDebugEnabled())
			mLogger.debug("AL sw: " + lemma);
		mTimeExplanations += System.nanoTime() - start;
		return lemma;
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public void printStatistics(Logger logger) {
		if (logger.isInfoEnabled()) {
			logger.info(String.format(
					"Array: #Arrays: %d, #BuildWeakEQ: %d, #ModEdges: %d, "
					+ "#addStores: %d, #merges: %d", mNumArrays,
					mNumBuildWeakEQ, mNumModuloEdges, mNumAddStores, mNumMerges));
			logger.info(String.format(
					"Insts: ReadOverWeakEQ: %d, WeakeqExt: %d",
					mNumInstsSelect, mNumInstsEq));
			logger.info(String.format("Time: BuildWeakEq: %.3f ms, BuildWeakEqi: %.3f ms",
					mTimeBuildWeakEq / 1e6, mTimeBuildWeakEqi / 1e6));
			logger.info(String.format("Time: Propagation %.3f ms, Explanations: %.3f ms",
					mTimePropagation / 1e6, mTimeExplanations / 1e6));
		}

	}

	@Override
	public void dumpModel(Logger logger) {
		if (!logger.isInfoEnabled())
			return;
		for (Entry<ArrayNode, Map<CCTerm, Object>> entry : mArrayModels.entrySet()) {
			StringBuilder sb = new StringBuilder();
			sb.append(entry.getKey().mTerm).append(" = store[");
			sb.append(((ArrayNode)entry.getValue().get(null)).mTerm);
			for (Entry<CCTerm, Object> storeEntry : entry.getValue().entrySet()) {
				if (storeEntry.getKey() == null)
					continue;
				sb.append(",(").append(storeEntry.getKey()).append(":=")
					.append(storeEntry.getValue()).append(')');
			}
			sb.append(']');
			logger.info(sb.toString());
		}
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public Clause backtrackComplete() {
		mPropClauses.clear();
		return null;
	}

	@Override
	public void restart(int iteration) {
		// Nothing to do
	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// Nothing to do
	}

	@Override
	public Object push() {
		mArrays.beginScope();
		mStores.beginScope();
		mDiffs.beginScope();
		return Integer.valueOf(mNumArrays);
	}

	@Override
	public void pop(Object object, int targetlevel) {
		mNumArrays = ((Integer) object).intValue();
		mStores.endScope();
		mArrays.endScope();
		mDiffs.endScope();
	}

	@Override
	public Object[] getStatistics() {
		return new Object[]{
			":Array", new Object[][]{
				{"NumArrays", mNumArrays},
				{"BuildWeakEQ", mNumBuildWeakEQ},
				{"AddStores", mNumAddStores},
				{"Merges", mNumMerges},
				{"ModuloEdges", mNumModuloEdges},
				{"ReadOverWeakeq", mNumInstsSelect},
				{"WeakeqExt", mNumInstsEq},
				{"Times", new Object[][]{
					{"BuildWeakEq", mTimeBuildWeakEq},
					{"BuildWeakEqi", mTimeBuildWeakEqi},
					{"Propagation", mTimePropagation},
					{"Explanations", mTimeExplanations}
				}}
			}};
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		HashMap<ArrayNode, Integer> freshIndices =
				new HashMap<ArrayNode, Integer>();
		HashMap<ArrayNode, Integer> freshValues =
				new HashMap<ArrayNode, Integer>();
		HashMap<ArrayNode, Set<CCTerm>> storeIndices =
				new HashMap<ArrayNode, Set<CCTerm>>();
		for (Entry<ArrayNode, Map<CCTerm, Object>> e 
				: mArrayModels.entrySet()) {

			ArrayNode root = (ArrayNode) e.getValue().get(null);
			Set<CCTerm> stores = storeIndices.get(root);
			if (stores == null) {
				stores = new HashSet<CCTerm>();
				storeIndices.put(root, stores);
			}
			/* Collect the indices for which a store that explicitly stores
			 * a zero value exists.  We need to set the values for the
			 * root at these indices to a fresh value.
			 *
			 * In our paper we set all indices for which a store exists to a 
			 * fresh value, but this is enough.
			 */
			for (Entry<CCTerm, Object> mapping : e.getValue().entrySet()) {
				if (mapping.getValue() instanceof CCTerm) {
					assert ((CCTerm) mapping.getValue()).isRepresentative();
					int val = ((CCTerm) mapping.getValue()).mModelVal;
					if (val == 0) {
						stores.add(mapping.getKey());
					}
				}
			}
		}
		for (Entry<ArrayNode, Map<CCTerm, Object>> e 
				: mArrayModels.entrySet()) {
			CCTerm ccterm = e.getKey().mTerm;
			assert ccterm.isRepresentative();
			Sort arraySort = ccterm.toSMTTerm(mClausifier.getTheory()).getSort();
			ArraySortInterpretation interp = 
					model.getArrayInterpretation(arraySort);
			ArrayValue aval = interp.getValue(ccterm.mModelVal);
			ArrayNode root = (ArrayNode) e.getValue().get(null);
			if (!freshIndices.containsKey(root)) {
				int idx = interp.getIndexInterpretation().extendFresh();
				freshIndices.put(root, idx);
			}
			interp.getValueInterpretation().ensureCapacity(2);
			aval.store(freshIndices.get(root), 1);
			Set<CCTerm> storeIdxs = storeIndices.get(root);
			for (CCTerm index : storeIdxs) {
				if (!e.getValue().containsKey(index)) {
					if (!freshValues.containsKey(root)) {
						freshValues.put(root, 
								interp.getValueInterpretation().extendFresh());
					}
					int val = freshValues.get(root);
					aval.store(index.mModelVal, val);
				}
			}
			for (Entry<CCTerm, Object> mapping : e.getValue().entrySet()) {
				CCTerm index = mapping.getKey();
				if (index == null)
					continue;
				assert index.isRepresentative();
				Object value = mapping.getValue();
				int val;
				if (value instanceof CCTerm) {
					assert ((CCTerm) value).isRepresentative();
					val = ((CCTerm) value).mModelVal;
				} else {
					ArrayNode weaki = (ArrayNode) value;
					if (!freshValues.containsKey(weaki)) {
						freshValues.put(weaki, 
								interp.getValueInterpretation().extendFresh());
					}
					val = freshValues.get(weaki);
				}
				aval.store(index.mModelVal, val);
			}
		}
	}
	
	public void notifyArray(CCTerm array, boolean isStore) {
		if (isStore) {
			mStores.add((CCAppTerm) array);
			mNumAddStores++;
		}
		mArrays.add(array);
		mNumArrays++;
	}
	
	public void notifyDiff(CCAppTerm diff) {
		mDiffs.add(diff);
	}
	
	static CCTerm getArrayFromSelect(CCAppTerm select) {
		return ((CCAppTerm) select.getFunc()).getArg();
	}

	static CCTerm getIndexFromSelect(CCAppTerm select) {
		return select.getArg();
	}
	
	static CCTerm getArrayFromStore(CCAppTerm store) {
		return ((CCAppTerm) ((CCAppTerm) 
				store.getFunc()).getFunc()).getArg();
	}
	
	static CCTerm getIndexFromStore(CCAppTerm store) {
		return ((CCAppTerm) store.getFunc()).getArg();
	}
	
	static CCTerm getValueFromStore(CCAppTerm store) {
		return store.getArg();
	}
	
	static CCTerm getLeftFromDiff(CCAppTerm diff) {
		return getIndexFromStore(diff);
	}
	
	static CCTerm getRightFromDiff(CCAppTerm diff) {
		return diff.getArg();
	}
	
	static Sort getArraySortFromSelect(CCAppTerm select) {
		return ((CCBaseTerm) ((CCAppTerm) select.getFunc()).getFunc())
				.getFunctionSymbol().getParameterSorts()[0];
	}
	
	static Sort getArraySortFromStore(CCAppTerm store) {
		return getArraySortFromSelect((CCAppTerm) store.getFunc());
	}
	
	private boolean merge(CCAppTerm store) {
		CCTerm array = getArrayFromStore(store);
		ArrayNode arrayNode = mCongRoots.get(array.getRepresentative());
		ArrayNode storeNode = mCongRoots.get(store.getRepresentative());
		if (arrayNode == storeNode)
			return false;
		
		mNumMerges++;
		if (mLogger.isDebugEnabled())
			mLogger.debug("Merge: ["
					+ getIndexFromStore(store).getRepresentative() + "] "
					+ arrayNode + " and " + storeNode);
		
		arrayNode.makeWeakRepresentative();
		storeNode.makeWeakRepresentative();

		Set<SymmetricPair<CCAppTerm>> propEqualities = 
				new HashSet<SymmetricPair<CCAppTerm>>();
		if (arrayNode.mStoreEdge == null) {
			if (mLogger.isDebugEnabled())
				mLogger.debug("  StoreEdge");
			// Combine the arrayNode and storeNode.
			arrayNode.mergeWith(storeNode, store, propEqualities);
		} else {
			// This means that storeNode and arrayNode are weak equivalent.
			// Otherwise arrayNode would have stayed its representative.
			// We need to insert appropriate select edges.
			
			HashSet<CCTerm> seenIndices = new HashSet<CCTerm>();
			CCTerm storeIndex = getIndexFromStore(store).getRepresentative();
			seenIndices.add(storeIndex);
			ArrayNode node = arrayNode;
			while (node.mStoreEdge != null) {
				CCTerm index = getIndexFromStore(node.mStoreReason)
						.getRepresentative();
				/* add the index to the seen indices and merge weak-i
				 * equivalence classes if index was not seen before and they
				 * are not already the same.
				 */
				if (seenIndices.add(index)
						&& node.getWeakIRepresentative(index) != storeNode) {
					mNumModuloEdges++;
					if (mLogger.isDebugEnabled())
						mLogger.debug("  SelectEdge: ["
								+ index + "] "
								+ node + " to " + storeNode);
					node.mergeSelect(storeNode, store, propEqualities);
				}
				node = node.mStoreEdge;
			}
		}
		for (SymmetricPair<CCAppTerm> equality : propEqualities) {
			CCAppTerm select1 = equality.getFirst();
			CCAppTerm select2 = equality.getSecond();
			if (select1.getRepresentative() == select2.getRepresentative())
				continue;
			CCTerm index1 = getIndexFromSelect(select1);
			CCTerm array1 = getArrayFromSelect(select1);
			CCTerm array2 = getArrayFromSelect(select2);
			Set<CCTerm> storeIndices = new HashSet<CCTerm>();
			computeStoreIndices(index1.getRepresentative(), array1, array2, storeIndices);
			Set<CCEquality> propClause = new HashSet<CCEquality>();
			for (CCTerm idx : storeIndices) {
				assert index1.getRepresentative() != idx.getRepresentative();
				CCEquality lit = createEquality(index1, idx);
				if (lit != null) {
					assert lit.getDecideStatus() != lit;
					if (lit.getDecideStatus() == null)
						propClause.add(lit);
				}
			}
			CCEquality lit = createEquality(select1, select2);
			if (lit != null) {
				assert lit.getDecideStatus() != lit;
				if (lit.getDecideStatus() == null)
					propClause.add(lit);
			}
			ArrayLemma lemma = new ArrayLemma();
			lemma.mUndecidedLits = propClause;
			lemma.mPropagatedEq = equality;
			mPropClauses.add(lemma);
		}
		return !propEqualities.isEmpty();
	}
	
	private CCEquality createEquality(CCTerm t1, CCTerm t2) {
		EqualityProxy ep = t1.getFlatTerm().createEquality(t2.getFlatTerm());
		if (ep == EqualityProxy.getFalseProxy())
				return null;
		Literal res = ep.getLiteral();
		if (res instanceof CCEquality) {
			CCEquality eq = (CCEquality) res;
			if ((eq.getLhs() == t1 && eq.getRhs() == t2)
					|| (eq.getLhs() == t2 && eq.getRhs() == t1))
				return eq;
		}
		return ep.createCCEquality(t1.getFlatTerm(), t2.getFlatTerm());
	}

	/**
	 * Auxiliary class to find the path between two array nodes for
	 * a given store index.
	 *
	 */
	private class Cursor {
		ArrayNode mNode;

		public Cursor(CCTerm term, ArrayNode node) {
			this.mNode = node;
		}
		
		/**
		 * Collect the store indices from this to dest over their
		 * common root using only the store edges.  The arrays must be
		 * weakly equivalent.
		 * @param array1 the first array.
		 * @param array2 the second array.
		 * @param storeIndices a map where the store indices are collected to.
		 */
		public void collectOverStores(ArrayNode destNode, Set<CCTerm> storeIndices) {
			int steps1 = mNode.countStoreEdges();
			int steps2 = destNode.countStoreEdges();
			while (steps1 > steps2) {
				storeIndices.add(getIndexFromStore(mNode.mStoreReason));
				mNode = mNode.mStoreEdge;
				steps1--;
			}
			while (steps2 > steps1) {
				storeIndices.add(getIndexFromStore(destNode.mStoreReason));
				destNode = destNode.mStoreEdge;
				steps2--;
			}
			while (mNode != destNode) {
				storeIndices.add(getIndexFromStore(mNode.mStoreReason));
				storeIndices.add(getIndexFromStore(destNode.mStoreReason));
				mNode = mNode.mStoreEdge;
				destNode = destNode.mStoreEdge;
			}
		}
		
		public void collectOneSelect(CCTerm index, Set<CCTerm> storeIndices) {
			ArrayNode selectNode = mNode.findSelectNode(index);
			CCAppTerm store = selectNode.mSelectReason;
			CCTerm array = getArrayFromStore(store);
			ArrayNode arrayNode = mCongRoots.get(array.getRepresentative());
			ArrayNode storeNode = mCongRoots.get(store.getRepresentative());
			if (arrayNode.findSelectNode(index) == selectNode) {
				collectOverStores(arrayNode, storeIndices);
				mNode = storeNode;
			} else {
				assert storeNode.findSelectNode(index) == selectNode;
				collectOverStores(storeNode, storeIndices);
				mNode = arrayNode;
			}
			storeIndices.add(getIndexFromStore(store));
		}

		/**
		 * Collect the store indices on the path from this to dest using
		 * only indices different from index. 
		 * @param index  the select index of the selects whose equality is propagated.
		 * @param dest the cursor for the second array.
		 * @param storeIndices initially an empty map.  All store indices are added
		 * to this map as side-effect.
		 */
		public void collect(CCTerm index, Cursor dest, Set<CCTerm> storeIndices) {
			int steps1 = mNode.countSelectEdges(index);
			int steps2 = dest.mNode.countSelectEdges(index);
			while (steps1 > steps2) {
				this.collectOneSelect(index, storeIndices);
				steps1--;
			}
			while (steps2 > steps1) {
				dest.collectOneSelect(index, storeIndices);
				steps2--;
			}
			while (mNode.findSelectNode(index) 
					!= dest.mNode.findSelectNode(index)) {
				this.collectOneSelect(index, storeIndices);
				dest.collectOneSelect(index, storeIndices);
			}
			this.collectOverStores(dest.mNode, storeIndices);
		}
	}

	/**
	 * Collect the store indices on the path from array1 to array2 using
	 * only indices different from index. 
	 * @param index  the select index of the selects whose equality is propagated.
	 * @param array1 the first array.
	 * @param array2 the second array.
	 * @param storeIndices initially an empty map.  All store indices are added
	 * to this map as side-effect.
	 */
	private void computeStoreIndices(CCTerm index, CCTerm array1,
			CCTerm array2, Set<CCTerm> storeIndices) {
		ArrayNode node1 = mCongRoots.get(array1.getRepresentative());
		ArrayNode node2 = mCongRoots.get(array2.getRepresentative());
		Cursor cursor1 = new Cursor(array1, node1); 
		Cursor cursor2 = new Cursor(array2, node2); 
		assert index == index.getRepresentative();
		cursor1.collect(index, cursor2, storeIndices);
	}

	private boolean buildWeakEq() {
		mNumBuildWeakEQ++;
		long startTime = System.nanoTime();
		mCongRoots = new HashMap<CCTerm, ArrayNode>();
		for (CCTerm array : mArrays) {
			CCTerm rep = array.getRepresentative();
			if (!mCongRoots.containsKey(rep)) {
				ArrayNode node = new ArrayNode(rep);
				node.computeSelects(mSelectFunNum);
				mCongRoots.put(rep, node);
			}
		}
		boolean res = false;
		for (CCAppTerm store : mStores) {
			res |= merge(store);
		}
		mTimeBuildWeakEq += (System.nanoTime() - startTime);
		return res;
	}
	
	/**
	 * Compute all weakeq-ext instances.
	 * @return <code>true</code> if and only if we found a new instance.
	 */
	private boolean computeWeakeqExt() {
		long startTime = System.nanoTime();
		mArrayModels = new HashMap<ArrayNode, Map<CCTerm,Object>>();
		HashMap<Map<CCTerm,Object>,ArrayNode> inverse = 
				new HashMap<Map<CCTerm,Object>, ArrayNode>();
		HashSet<SymmetricPair<ArrayNode>> propEqualities = 
				new HashSet<SymmetricPair<ArrayNode>>();
		ArrayDeque<ArrayNode> todoQueue = 
				new ArrayDeque<ArrayNode>(mCongRoots.values());
		while (!todoQueue.isEmpty()) {
			ArrayNode node = todoQueue.getFirst();
			if (mArrayModels.containsKey(node)) {
				todoQueue.removeFirst();
				continue;
			}
			if (node.mStoreEdge != null
				&& !mArrayModels.containsKey(node.mStoreEdge)) {
				todoQueue.addFirst(node.mStoreEdge);
				continue;
			}
			todoQueue.removeFirst();
			HashMap<CCTerm, Object> nodeMapping
				= new HashMap<CCTerm, Object>();
			if (node.mStoreEdge == null) {
				nodeMapping.put(null, node);
				for (Entry<CCTerm, CCAppTerm> e : node.mSelects.entrySet()) {
					nodeMapping.put(e.getKey(), e.getValue().getRepresentative());
				}
			} else {
				CCTerm storeIndex = getIndexFromStore(node.mStoreReason)
						.getRepresentative();
				nodeMapping.putAll(mArrayModels.get(node.mStoreEdge));
				nodeMapping.remove(storeIndex);
				ArrayNode weakiRep = node.getWeakIRepresentative(storeIndex);
				CCAppTerm value = weakiRep.mSelects.get(storeIndex);
				if (value != null) { //NOPMD
					nodeMapping.put(storeIndex, value.getRepresentative());
				} else if (weakiRep.mStoreEdge != null) {
					nodeMapping.put(storeIndex, weakiRep);
				}
			}
			mArrayModels.put(node, nodeMapping);
			ArrayNode prev = inverse.put(nodeMapping, node);
			if (prev != null) {
				propEqualities.add(new SymmetricPair<ArrayNode>(prev, node));
			}
		}
		for (SymmetricPair<ArrayNode> equalities : propEqualities) {
			mNumInstsEq++;
			WeakCongruencePath path = new WeakCongruencePath(this);
			Clause lemma = path.computeWeakeqExt(
					equalities.getFirst().mTerm, equalities.getSecond().mTerm,
					mCClosure.mEngine.isProofGenerationEnabled());
			if (mLogger.isDebugEnabled())
				mLogger.debug("AL sw: " + lemma);
			mCClosure.mEngine.learnClause(lemma);
		}
		mTimeBuildWeakEqi += (System.nanoTime() - startTime);
		return !propEqualities.isEmpty();
	}

	CClosure getCClosure() {
		return mCClosure;
	}
	
	Clausifier getClausifier() {
		return mClausifier;
	}
	
	boolean isStore(CCTerm term) {
		return mStores.contains(term);
	}
	
	private void cleanCaches() {
		mCongRoots = null;
		mPropClauses.clear();
	}
}
