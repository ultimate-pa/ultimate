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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArrayValue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

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
	 * <p>
	 * The core data structure used by the array theory solver. For every strong term equivalence class of an array
	 * sort, we create an ArrayNode representing this array. The ArrayNodes are connected by primary store edges, which
	 * form a spanning tree of the weak equivalence class pointing to the weak representative. The primary edges always
	 * combine the ArrayNode representing the store with the ArrayNode representing the array of the store. The
	 * direction of the edge may be inverted, though.
	 * </p>
	 * 
	 * <p>
	 * In addition there are so called secondary edges that are induced by another store (mSecondaryStore) on a
	 * different index than the store that induces the store edge. For a given index, if we would remove all primary
	 * edges on that index, the weak equivalence graph would fall into some smaller equivalence classes. The roots of
	 * the smaller equivalence classes are the original root and the array nodes whose mStoreEdge is on the index. We
	 * now combine these smaller equivalence classes by adding secondary edges from the root of one small equivalence
	 * class to an arbitrary node in the other equivalence class, building a new weak-i equivalence class, which is a
	 * subset of the whole weak equivalence class. The original root is the root of its weak-i equivalence class for
	 * every index, but there may be others weak-i equivalence class roots that are characterized by having a primary
	 * but no secondary edge. The store and array of the secondary edge are guaranteed to be reachable from the origin
	 * and destination of the select edge by using only primary edges on a different index. A single store can cause
	 * several secondary edges for different i's (all different from the index of the store) so different array nodes
	 * may have the same secondary store.
	 * </p>
	 * 
	 * <p>
	 * The primary and secondary edges induce for every index and every pair of arrays in the same weak-i equivalence
	 * class for that index a unique path that connects the arrays only by stores on a different index.
	 * </p>
	 * 
	 * <p>
	 * There is exactly only one ArrayNode for each strong equivalence class with array sort, and the CCTerm data
	 * structure is used to find the representative of the strong equivalence class. To find the representative of the
	 * weak equivalence class, the primary edges can be followed. The representative of a weak equivalence class for an
	 * index i is found by following the primary edges if the primary store index is different from i, and following the
	 * secondary edge otherwise. If there is no secondary edge and the primary index equals i, or there is no primary
	 * edge, then the weak-i representative has been found.
	 * </p>
	 * 
	 * @author Jochen Hoenicke
	 *
	 */
	class ArrayNode {
		/**
		 * The ccterm this node corresponds to. 
		 * This is always the representative, i.e.,
		 * <code>mTerm.repStar = mTerm</code>.
		 */
		CCTerm mTerm;
		
		/**
		 * The destination node of the primary edge.
		 */
		ArrayNode mPrimaryEdge;
		
		/**
		 * The store corresponding to the primary edge. This must be a CCAppTerm of a store. Also the both the store
		 * term and the array parameter of the store must be elements of mTerm.mMembers resp.
		 * mPrimaryEdge.mTerm.mMembers. It is not guaranteed which of these two terms belongs to which equivalence
		 * class, because we want to be able to reverse edges.
		 */
		CCAppTerm mPrimaryStore;
		
		/**
		 * The secondary edge pointing towards the representative in the weak-i equivalence group, where <code>i</code>
		 * is the index of primary store term. The secondary edges are used to find the weak-i representative, if the
		 * primary reason involves the index i. If it does not, the primary edge should be followed.
		 * 
		 * This is null for the weak-i representative. The weak representative is also a weak-i representative for all
		 * indices.
		 */
		ArrayNode mSecondaryEdge;
		
		/**
		 * The store corresponding to the primary edge. If secondary edge is set, this must be a CCAppTerm of a store.
		 * The index must be different from the primary store index. Again it is not guaranteed if the store corresponds
		 * to the source or the destination of the secondary edge. The term that corresponds to this array node is not
		 * necessarily in mTerm.mMembers, but it is guaranteed that it is in some {@code node.mTerm.mMembers}, such that
		 * this is reachable from node using only primary edges and the primary store indices differ from this primary
		 * store index.
		 */
		CCAppTerm mSecondaryStore;
		
		/**
		 * The array nodes in the same weak equivalence class form a cyclic 
		 * linked list by virtue of this pointer.
		 */
		ArrayNode mNext;
		
		/**
		 * A map from index to the selects that exists for this weak-i equivalence class. Used to quickly merge weak-i
		 * classes and to quickly compute new equivalences. We only have to remember one of the select terms for each
		 * index, since the other are supposed to be equal.
		 * 
		 * The key is always the representative of the index of the corresponding select.
		 * 
		 * This is an arbitrary map for weak representative (no primary edge), should be a singleton for weak-i
		 * representatives (primary edge exists, but no seconddary edge) and empty for all other nodes (where both edges
		 * exist).
		 */
		Map<CCTerm, CCAppTerm> mSelects;

		CCAppTerm mConstTerm;

		/**
		 * Create a new array term corresponding to a ccterm.
		 * @param ccterm the corresponding ccterm.  This must be its own
		 * representative.
		 */
		public ArrayNode(CCTerm ccterm) {
			assert ccterm.isRepresentative();
			mTerm = ccterm;
			mNext = this;
			mPrimaryEdge = mSecondaryEdge = null;
			mPrimaryStore = null;
		}

		/**
		 * Fill the select information for the current node. This needs to be called when a new array node is created.
		 * It finds all select applications using the ccterm information and adds them to the mSelects hash map.
		 * 
		 * @param mSelectFunNum
		 *            the index of the first argument of the builtin select function in the parent info datastructure in
		 *            ccterm.
		 */
		public void computeSelects(int mSelectFunNum) {
			mSelects = new HashMap<CCTerm, CCAppTerm>();
			final CCParentInfo info = mTerm.mCCPars.getExistingParentInfo(mSelectFunNum);
			if (info != null) {
				for (final CCAppTerm.Parent pa : info.mCCParents) {
					final CCParentInfo selectas = pa.getData().getRepresentative().mCCPars.getExistingParentInfo(0);
					for (final CCAppTerm.Parent spa : selectas.mCCParents) {
						final CCAppTerm select = spa.getData();
						assert (getArrayFromSelect(select).getRepresentative() == mTerm);
						assert (select != null);
						mSelects.put(select.mArg.getRepresentative(), select);
					}
				}
			}
		}

		/**
		 * Get the representative of the weak equivalence class. This is the root of the tree formed by mStoreEdge.
		 * 
		 * @return the representative array node.
		 */
		public ArrayNode getWeakRepresentative() {
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				node = node.mPrimaryEdge;
			}
			return node;
		}

		/**
		 * Get the representative of the weak-i equivalence class. This is an ArrayNode that is connected by a sequence
		 * of stores on indices different from the given index. Thus it stores the same value for a select on the given
		 * index.
		 * 
		 * @param index
		 *            the index i for which the weak-i equivalence class representative should be returned.
		 * @return the representative array node.
		 */
		public ArrayNode getWeakIRepresentative(CCTerm index) {
			index = index.getRepresentative();
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				if (getIndexFromStore(node.mPrimaryStore).getRepresentative() == index) {
					if (node.mSecondaryEdge == null) {
						break;
					}
					node = node.mSecondaryEdge;
				} else {
					node = node.mPrimaryEdge;
				}
			}
			return node;
		}

		/**
		 * Make this node its weak-i representative, by inverting all select edges pointing outwards. This assumes, that
		 * the node is not yet a weak-i representative (and thus not the weak representative), and that the weak
		 * representative is not in the same weak-i equivalence class, i.e., the weak-i representative is not the
		 * current weak representative.
		 */
		public void makeWeakIRepresentative() {
			assert mPrimaryEdge != null;
			assert mSecondaryEdge != null;
			final CCTerm index = getIndexFromStore(mPrimaryStore).getRepresentative();
			assert getWeakIRepresentative(index) != getWeakRepresentative();
			ArrayNode prev = this;
			ArrayNode next = prev.mSecondaryEdge;
			CCAppTerm prevReason = prev.mSecondaryStore;
			while (next != null) {
				// first follow the primary edges until we find the a store on the index.
				next = next.findSecondaryNode(index);

				// now copy the new edge information
				final ArrayNode nextEdge = next.mSecondaryEdge;
				final CCAppTerm nextReason = next.mSecondaryStore;
				// invert the previous edge
				next.mSecondaryEdge = prev;
				next.mSecondaryStore = prevReason;
				// continue inverting
				prev = next;
				prevReason = nextReason;
				next = nextEdge;
			}
			mSecondaryEdge = null;
			mSecondaryStore = null;
			mSelects = prev.mSelects;
			prev.mSelects = Collections.emptyMap();
		}

		/**
		 * Make this array node the representative of its weak equivalence
		 * group by inverting all the store edges.
		 */
		public void makeWeakRepresentative() {
			if (mPrimaryEdge == null) {
				return;
			}
			// hash map from store indices we have seen on the primary path to the previous destination/new source of
			// the primary edge (or in other words, to the new candidate for weak-i equivalence class).
			final HashMap<CCTerm, ArrayNode> seenStores = new HashMap<CCTerm, ArrayNode>();
			// for each index, the information about secondary edge that we later need to invert.
			final HashMap<CCTerm, ArrayNode> todoSecondary = new HashMap<CCTerm, ArrayNode>();
			final HashMap<CCTerm, CCAppTerm> todoSecondaryStores = new HashMap<CCTerm, CCAppTerm>();
			// the select information for the new root node.
			final HashMap<CCTerm, CCAppTerm> newSelectMap = new HashMap<CCTerm, CCAppTerm>();
			ArrayNode node = this;
			ArrayNode prev = null;
			CCAppTerm prevStore = null;
			while (node.mPrimaryEdge != null) {
				// invert the last primary edge
				final ArrayNode next = node.mPrimaryEdge;
				final CCAppTerm nextStore = node.mPrimaryStore;
				node.mPrimaryEdge = prev;
				node.mPrimaryStore = prevStore;

				final CCTerm index = getIndexFromStore(nextStore).getRepresentative();
				final ArrayNode old = seenStores.put(index, next);
				if (old == node) {
					// the node is in the middle of two consecutive stores on the same
					// index. There is no need to move the secondary information
					// around.
					//
					// This branch is intentionally left empty!
				} else if (node.mSecondaryEdge != null) { //NOPMD
					if (old == null) {
						// we have to invert the secondary edge in the end, but
						// we should wait until the inversion of the primary edges
						// is completed.
						todoSecondary.put(index, node.mSecondaryEdge);
						todoSecondaryStores.put(index, node.mSecondaryStore);
					} else {
						// insert the secondary edge of node into old node. The reasoning is that
						// the old node is connected using only primary edges on different indices, so it has
						// the same weak-i representative as node.
						assert (getIndexFromStore(old.mPrimaryStore).getRepresentative() == index);
						assert (old.mSecondaryEdge == null);
						old.mSecondaryEdge = node.mSecondaryEdge;
						old.mSecondaryStore = node.mSecondaryStore;
					}
					node.mSecondaryEdge = null;
					node.mSecondaryStore = null;
				} else if (!node.mSelects.isEmpty()) {
					if (old == null) {
						// assertion holds, because index was not in seenStores.
						assert node.mSelects.get(index) != null;
						// we need to move the select information into the new root node.
						newSelectMap.put(index, node.mSelects.get(index)); 
					} else {
						// old is weak-i equivalent to node and can be used as new weak-i representative.
						old.mSelects = node.mSelects;
					}
					node.mSelects = Collections.emptyMap();
				}

				prev = node;
				node = next;
				prevStore = nextStore;
			}
			node.mPrimaryEdge = prev;
			node.mPrimaryStore = prevStore;
			mConstTerm = node.mConstTerm;
			node.mConstTerm = null;
			final Map<CCTerm, CCAppTerm> rootSelects = node.mSelects;
			node.mSelects = Collections.emptyMap();
			for (final Entry<CCTerm, ArrayNode> entry : seenStores.entrySet()) {
				// The seen stores get the new representatives of their weak-i equivalence groups
				final CCTerm index = entry.getKey();
				final CCAppTerm select = rootSelects.remove(index);
				if (select != null) {
					entry.getValue().mSelects = 
						Collections.singletonMap(index, select);
				}
			}
			// Now invert the secondary edges
			for (final Entry<CCTerm, ArrayNode> entry : todoSecondary.entrySet()) {
				final CCTerm index = entry.getKey();
				ArrayNode dest = entry.getValue();
				dest = dest.findSecondaryNode(index);
				if (dest.mSecondaryEdge != null) {
					dest.makeWeakIRepresentative();
				}
				dest.mSecondaryEdge = this;
				dest.mSecondaryStore = todoSecondaryStores.get(index);
				newSelectMap.putAll(dest.mSelects);
				dest.mSelects = Collections.emptyMap();
			}
			newSelectMap.putAll(rootSelects);
			mSelects = newSelectMap;
		}

		/**
		 * Add a primary edge from this node to storeNode. Both nodes should be the weak equivalent root when this is
		 * called.
		 * 
		 * @param storeNode
		 *            The destination node
		 * @param store
		 *            The store term that caused this edge
		 * @param propLemmas
		 *            A collection where propagated array lemmas are added to by this method.
		 */
		public void mergeWith(ArrayNode storeNode, CCAppTerm store, Collection<ArrayLemma> propLemmas) {
			assert mPrimaryEdge == null && storeNode.mPrimaryEdge == null;
			mPrimaryEdge = storeNode;
			mPrimaryStore = store;

			// merge next linkage
			final ArrayNode next = mNext;
			mNext = storeNode.mNext;
			storeNode.mNext = next;

			// merge the consts;
			// this map collects all selects in the other class, that may need to be merge with the const.
			Map<CCTerm, CCAppTerm> mergeConstSelects = new HashMap<>();
			if (mConstTerm != null) {
				if (storeNode.mConstTerm == null) {
					storeNode.mConstTerm = mConstTerm;
					mConstTerm = null;
					mergeConstSelects.putAll(storeNode.mSelects);
				} else {
					CCTerm const1 = getValueFromConst(mConstTerm);
					CCTerm const2 = getValueFromConst(storeNode.mConstTerm);
					if (const1.getRepresentative() != const2.getRepresentative()) {
						propLemmas.add(new ArrayLemma(RuleKind.CONST_WEAKEQ, const1, const2));
					}
				}
			} else if (storeNode.mConstTerm != null) {
				mergeConstSelects.putAll(this.mSelects);
			}
			mergeConstSelects.remove(getIndexFromStore(store).getRepresentative());

			// merge the selects;
			Map<CCTerm, CCAppTerm> newSelects = Collections.emptyMap();
			for (final Entry<CCTerm, CCAppTerm> entry : mSelects.entrySet()) {
				final CCTerm index = entry.getKey();
				final CCAppTerm select = entry.getValue();
				assert select != null;
				if (index == getIndexFromStore(store).getRepresentative()) {
					newSelects = Collections.singletonMap(index, select);
				} else {
					final CCAppTerm otherSelect = storeNode.mSelects.get(index);
					if (otherSelect == null) {
						// move the select to new representative.
						storeNode.mSelects.put(index, select);
					} else {
						mergeConstSelects.remove(index);
						if (select.getRepresentative() != otherSelect.getRepresentative()) {
							// add propagated equality
							propLemmas.add(new ArrayLemma(RuleKind.READ_OVER_WEAKEQ, select, otherSelect));
						}
					}
				}
			}
			mSelects = newSelects;
			if (storeNode.mConstTerm != null) {
				CCTerm const1 = getValueFromConst(storeNode.mConstTerm);
				ArrayNode constNode = mCongRoots.get(storeNode.mConstTerm.getRepresentative());
				for (final Entry<CCTerm, CCAppTerm> entry : mergeConstSelects.entrySet()) {
					final CCTerm index = entry.getKey();
					final CCAppTerm select = entry.getValue();
					// check if selected array is weakly equal to the const array
					if (constNode.getWeakIRepresentative(index) == storeNode) {
						// do not keep select, we will merge it with the constant value
						storeNode.mSelects.remove(index);
						if (select.getRepresentative() != const1.getRepresentative()) {
							propLemmas.add(new ArrayLemma(RuleKind.READ_CONST_WEAKEQ, select, const1));
						}
					}
				}
			}
		}

		/**
		 * Add secondary edge from this node to storeNode. The storeNode should be the weak equivalent root. This node
		 * should be weak-i equivalent to the array in the store term where i is the index of the primary store. And the
		 * store should also be on a different index.
		 *
		 * @param storeNode
		 *            The destination node
		 * @param store
		 *            The store term that caused this edge
		 * @param propEqualities
		 *            A collection where propagated array lemmas are added to by this method.
		 */
		public void mergeSecondary(ArrayNode storeNode, CCAppTerm store, Collection<ArrayLemma> propEqualities) {
			assert storeNode.mPrimaryEdge == null;
			assert mPrimaryEdge != null;
			assert getIndexFromStore(mPrimaryStore).getRepresentative()
					!= getIndexFromStore(store).getRepresentative();
			if (mSecondaryEdge != null) {
				makeWeakIRepresentative();
			}
			mSecondaryEdge = storeNode;
			mSecondaryStore = store;
			final CCTerm storeIndex = getIndexFromStore(mPrimaryStore).getRepresentative();
			if (!mSelects.isEmpty()) {
				final CCAppTerm select = mSelects.get(storeIndex);
				assert (select != null);
				final CCAppTerm otherSelect = storeNode.mSelects.get(storeIndex);
				if (otherSelect == null) {
					storeNode.mSelects.put(storeIndex, select);
				} else {
					if (select.getRepresentative() != otherSelect.getRepresentative()) {
						propEqualities.add(new ArrayLemma(RuleKind.READ_OVER_WEAKEQ, select, otherSelect));
					}
				}
				mSelects = Collections.emptyMap();
			}
			if (storeNode.mConstTerm != null) {
				// We only need to merge a select and const, if the const term is now weak-i equivalent to the store
				// node.
				ArrayNode constNode = mCongRoots.get(storeNode.mConstTerm.getRepresentative());
				if (constNode.getWeakIRepresentative(storeIndex) == storeNode) {
					// do not keep select, we will merge it with the constant value
					CCAppTerm select = storeNode.mSelects.remove(storeIndex);
					CCTerm const1 = getValueFromConst(storeNode.mConstTerm);
					if (select != null && select.getRepresentative() != const1.getRepresentative()) {
						propEqualities.add(new ArrayLemma(RuleKind.READ_CONST_WEAKEQ, select, const1));
					}
				}
			}
		}

		/**
		 * Count the number of secondary edges to the weak-i equivalence class representative.
		 *
		 * @param index
		 *            the index i.
		 * @return the number of secondary edges from this to the weak-i root.
		 */
		public int countSecondaryEdges(CCTerm index) {
			assert index.isRepresentative();
			int count = 0;
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				if (getIndexFromStore(node.mPrimaryStore).getRepresentative() == index) {
					if (node.mSecondaryEdge == null) {
						break;
					}
					node = node.mSecondaryEdge;
					count++;
				} else {
					node = node.mPrimaryEdge;
				}
			}
			return count;
		}

		/**
		 * Find the next node on the primary chain where the primary edge uses the given index.
		 */
		public ArrayNode findSecondaryNode(CCTerm index) {
			assert index.isRepresentative();
			ArrayNode node = this;
			while (node.mPrimaryEdge != null && getIndexFromStore(node.mPrimaryStore).getRepresentative() != index) {
				node = node.mPrimaryEdge;
			}
			return node;
		}

		/**
		 * Count the number of primary edges to the weak equivalence class representative.
		 *
		 * @return the number of primary edges from this to the root.
		 */
		public int countPrimaryEdges() {
			int count = 0;
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				node = node.mPrimaryEdge;
				count++;
			}
			return count;
		}

		/**
		 * Returns the hash code.  This equals the hash code of the underlying
		 * ccterm.  Note that our algorithm guarantees that there is at most
		 * one ArrayTerm created for any ccterm.
		 */
		@Override
		public int hashCode() {
			return mTerm.hashCode();
		}

		@Override
		public String toString() {
			return "ArrayNode[" + mTerm + "]";
		}
	}

	private static class ArrayLemma {
		RuleKind mRule;
		SymmetricPair<CCTerm> mPropagatedEq;
		Set<CCEquality> mUndecidedLits;

		public ArrayLemma(RuleKind rule, CCTerm lhs, CCTerm rhs) {
			this.mRule = rule;
			this.mPropagatedEq = new SymmetricPair<CCTerm>(lhs, rhs);
		}

		public RuleKind getRule() {
			return mRule;
		}

		public SymmetricPair<CCTerm> getEquality() {
			return mPropagatedEq;
		}

		@Override
		public int hashCode() {
			return HashUtils.hashJenkins(mRule.hashCode(), mPropagatedEq);
		}

		public boolean equals(Object other) {
			if (other instanceof ArrayLemma) {
				ArrayLemma o = (ArrayLemma) other;
				return mRule == o.mRule && mPropagatedEq.equals(o.mPropagatedEq);
			}
			return false;
		}

		@Override
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
	private final ScopedHashSet<CCAppTerm> mConsts =
			new ScopedHashSet<CCAppTerm>();
	
	private final ArrayDeque<ArrayLemma> mPropClauses = 
			new ArrayDeque<ArrayLemma>();
	
	private final LogProxy mLogger;
	
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
			for (final ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.remove(literal.negate())
					&& lemma.mUndecidedLits.isEmpty()) {
					return explainPropagation(lemma);
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
			for (final ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.isEmpty()) {
					return explainPropagation(lemma);
				}
			}
		}
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		final Clause conflict = checkpoint();
		if (conflict != null) {
			return conflict;
		}
		if (mPropClauses.isEmpty()) {
			final boolean foundLemma = computeWeakeqExt();
			if (foundLemma) {
				mArrayModels = null;
			}
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		final long start = System.nanoTime();
		for (final ArrayLemma lemma : mPropClauses) {
			if (lemma.mUndecidedLits.size() == 1) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("AL prop: " + lemma);
				}
				final Literal lit = lemma.mUndecidedLits.iterator().next();
				mTimePropagation += System.nanoTime() - start;
				lit.getAtom().mExplanation = explainPropagation(lemma);
				return lit;
			}
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		assert literal instanceof CCEquality;
		if (mCongRoots == null) {
			buildWeakEq();
		}
		for (final ArrayLemma lemma : mPropClauses) {
			final Set<CCEquality> lits = lemma.mUndecidedLits;
			if (lits.isEmpty()
				|| (lits.size() == 1 && lits.contains(literal))) {
				return explainPropagation(lemma);
			}
		}
		throw new AssertionError("Cannot explain unit literal!");
	}

	private Clause explainPropagation(ArrayLemma lemma) {
		SymmetricPair<CCTerm> equality = lemma.getEquality();
		final long start = System.nanoTime();
		mNumInstsSelect++;
		final WeakCongruencePath path = new WeakCongruencePath(this);
		final Clause clause;
		switch (lemma.getRule()) {
		case READ_OVER_WEAKEQ:
			clause = path.computeSelectOverWeakEQ((CCAppTerm) equality.getFirst(), (CCAppTerm) equality.getSecond(),
					mCClosure.mEngine.isProofGenerationEnabled());
			break;
		case CONST_WEAKEQ:
			clause = path.computeConstOverWeakEQ(findConst(equality.getFirst()), findConst(equality.getSecond()),
					mCClosure.mEngine.isProofGenerationEnabled());
			break;
		case READ_CONST_WEAKEQ:
			clause = path.computeSelectConstOverWeakEQ((CCAppTerm) equality.getFirst(), findConst(equality.getSecond()),
					mCClosure.mEngine.isProofGenerationEnabled());
			break;
		default:
			throw new AssertionError("Unknown Lemma");
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("AL sw: " + clause);
		}
		mTimeExplanations += System.nanoTime() - start;
		return clause;
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		if (logger.isInfoEnabled()) {
			logger.info("Array: #Arrays: %d, #BuildWeakEQ: %d, #ModEdges: %d, "
					+ "#addStores: %d, #merges: %d", mNumArrays,
					mNumBuildWeakEQ, mNumModuloEdges, mNumAddStores, mNumMerges);
			logger.info("Insts: ReadOverWeakEQ: %d, WeakeqExt: %d",
					mNumInstsSelect, mNumInstsEq);
			logger.info("Time: BuildWeakEq: %.3f ms, BuildWeakEqi: %.3f ms",
					mTimeBuildWeakEq / 1e6, mTimeBuildWeakEqi / 1e6);
			logger.info("Time: Propagation %.3f ms, Explanations: %.3f ms",
					mTimePropagation / 1e6, mTimeExplanations / 1e6);
		}

	}

	@Override
	public void dumpModel(LogProxy logger) {
		if (!logger.isInfoEnabled()) {
			return;
		}
		for (final Entry<ArrayNode, Map<CCTerm, Object>> entry : mArrayModels.entrySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(entry.getKey().mTerm).append(" = store[");
			sb.append(((ArrayNode)entry.getValue().get(null)).mTerm);
			for (final Entry<CCTerm, Object> storeEntry : entry.getValue().entrySet()) {
				if (storeEntry.getKey() == null) {
					continue;
				}
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
		mConsts.beginScope();
		mDiffs.beginScope();
		return Integer.valueOf(mNumArrays);
	}

	@Override
	public void pop(Object object, int targetlevel) {
		mNumArrays = ((Integer) object).intValue();
		mArrays.endScope();
		mStores.endScope();
		mConsts.endScope();
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

	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		final HashMap<ArrayNode, Integer> freshIndices =
				new HashMap<ArrayNode, Integer>();
		final HashMap<ArrayNode, Integer> freshValues =
				new HashMap<ArrayNode, Integer>();
		final HashMap<ArrayNode, Set<CCTerm>> storeIndices =
				new HashMap<ArrayNode, Set<CCTerm>>();
		/* first create a fresh value for each array, unless it is the constant 0 array */
		final ArrayDeque<ArrayNode> todoQueue = new ArrayDeque<ArrayNode>(mArrayModels.keySet());
		while (!todoQueue.isEmpty()) {
			final ArrayNode node = todoQueue.removeFirst();
			final Sort arraySort = node.mTerm.toSMTTerm(t).getSort();
			final ArraySortInterpretation arraySortInterpretation =
					(ArraySortInterpretation) model.provideSortInterpretation(arraySort);
			if (node.mConstTerm == null) {
				/* if the node is not constant, create a fresh value for the node. */
				node.mTerm.mModelVal = arraySortInterpretation.createEmptyArrayValue();
				continue;
			}
			CCTerm constValueTerm = getValueFromConst(node.mConstTerm).getRepresentative();
			ArrayNode constValueArrayNode = mCongRoots.get(constValueTerm);
			if (constValueArrayNode != null && todoQueue.contains(constValueArrayNode)) {
				/* we need to evaluate that first */
				todoQueue.remove(constValueArrayNode);
				todoQueue.addFirst(node);
				todoQueue.addFirst(constValueArrayNode);
				continue;
			}
			if (constValueTerm.mModelVal == 0) {
				node.mTerm.mModelVal = 0;
			} else {
				node.mTerm.mModelVal = arraySortInterpretation.createEmptyArrayValue();
			}
		}
		for (final Entry<ArrayNode, Map<CCTerm, Object>> e 
				: mArrayModels.entrySet()) {
			final ArrayNode root = (ArrayNode) e.getValue().get(null);
			if (root.mConstTerm != null) {
				continue;
			}
			Set<CCTerm> stores = storeIndices.get(root);
			if (stores == null) {
				stores = new HashSet<CCTerm>();
				storeIndices.put(root, stores);
			}
			/*
			 * Collect the indices for which a store that explicitly stores a zero value exists. We need to set the
			 * values for the root at these indices to a fresh value.
			 *
			 * In our paper we set all indices for which a store exists to a fresh value, but this is enough.
			 * 
			 * But only do this if the array is not a constant array.
			 */
			for (final Entry<CCTerm, Object> mapping : e.getValue().entrySet()) {
				if (mapping.getValue() instanceof CCTerm) {
					assert ((CCTerm) mapping.getValue()).isRepresentative();
					final int val = ((CCTerm) mapping.getValue()).mModelVal;
					if (val == 0) {
						stores.add(mapping.getKey());
					}
				}
			}
		}
		for (final Entry<ArrayNode, Map<CCTerm, Object>> e 
				: mArrayModels.entrySet()) {
			final CCTerm ccterm = e.getKey().mTerm;
			assert ccterm.isRepresentative();
			final Sort arraySort = ccterm.toSMTTerm(mClausifier.getTheory()).getSort();
			final ArraySortInterpretation interp = 
					model.getArrayInterpretation(arraySort);
			final ArrayValue aval = interp.getValue(ccterm.mModelVal);
			final ArrayNode root = (ArrayNode) e.getValue().get(null);
			if (root.mConstTerm == null) {
				if (!freshIndices.containsKey(root)) {
					final int idx = interp.getIndexInterpretation().extendFresh();
					freshIndices.put(root, idx);
				}
				interp.getValueInterpretation().ensureCapacity(2);
				aval.store(freshIndices.get(root), 1);
				final Set<CCTerm> storeIdxs = storeIndices.get(root);
				for (final CCTerm index : storeIdxs) {
					if (!e.getValue().containsKey(index)) {
						if (!freshValues.containsKey(root)) {
							freshValues.put(root, interp.getValueInterpretation().extendFresh());
						}
						final int val = freshValues.get(root);
						aval.store(index.mModelVal, val);
					}
				}
			} else {
				CCTerm defaultValue = getValueFromConst(root.mConstTerm).getRepresentative();
				aval.setDefaultValue(defaultValue.mModelVal);
			}
			for (final Entry<CCTerm, Object> mapping : e.getValue().entrySet()) {
				final CCTerm index = mapping.getKey();
				if (index == null) {
					continue;
				}
				assert index.isRepresentative();
				final Object value = mapping.getValue();
				int val;
				if (value instanceof CCTerm) {
					assert ((CCTerm) value).isRepresentative();
					val = ((CCTerm) value).mModelVal;
				} else {
					final ArrayNode weaki = (ArrayNode) value;
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
	
	public void notifyArray(CCTerm array, boolean isStore, boolean isConst) {
		if (isStore) {
			mStores.add((CCAppTerm) array);
			mNumAddStores++;
		}
		if (isConst) {
			mConsts.add((CCAppTerm) array);
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

	static CCTerm getValueFromConst(CCAppTerm term) {
		return term.getArg();
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
	
	CCAppTerm findConst(CCTerm value) {
		for (CCAppTerm constTerm : mConsts) {
			if (value == getValueFromConst(constTerm))
				return constTerm;
		}
		throw new AssertionError("Constant term not found for " + value);
	}

	private void setConst(CCAppTerm term) {
		final CCTerm const1 = getValueFromConst(term);
		final CCTerm rep = term.getRepresentative();
		final ArrayNode node = mCongRoots.get(rep);
		if (node.mConstTerm != null) {
			CCTerm const2 = getValueFromConst(node.mConstTerm);
			if (const1.getRepresentative() != const2.getRepresentative()) {
				mPropClauses.add(new ArrayLemma(RuleKind.CONST_WEAKEQ, const1, const2));
			}
		} else {
			node.mConstTerm = term;
			for (CCAppTerm select : node.mSelects.values()) {
				if (select.getRepresentative() != const1.getRepresentative()) {
					mPropClauses.add(new ArrayLemma(RuleKind.READ_CONST_WEAKEQ, select, const1));
				}
			}
		}
	}

	private void merge(CCAppTerm store) {
		final CCTerm array = getArrayFromStore(store);
		final ArrayNode arrayNode = mCongRoots.get(array.getRepresentative());
		final ArrayNode storeNode = mCongRoots.get(store.getRepresentative());
		if (arrayNode == storeNode)
			return;
		
		mNumMerges++;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Merge: ["
					+ getIndexFromStore(store).getRepresentative() + "] "
					+ arrayNode + " and " + storeNode);
		}
		
		arrayNode.makeWeakRepresentative();
		storeNode.makeWeakRepresentative();

		if (arrayNode.mPrimaryEdge == null) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("  PrimaryEdge");
			}
			// Combine the arrayNode and storeNode.
			arrayNode.mergeWith(storeNode, store, mPropClauses);
		} else {
			// This means that storeNode and arrayNode are weak equivalent.
			// Otherwise arrayNode would have stayed its representative.
			// We need to insert appropriate select edges.
			
			final HashSet<CCTerm> seenIndices = new HashSet<CCTerm>();
			final CCTerm storeIndex = getIndexFromStore(store).getRepresentative();
			seenIndices.add(storeIndex);
			ArrayNode node = arrayNode;
			while (node.mPrimaryEdge != null) {
				final CCTerm index = getIndexFromStore(node.mPrimaryStore)
						.getRepresentative();
				/* add the index to the seen indices and merge weak-i
				 * equivalence classes if index was not seen before and they
				 * are not already the same.
				 */
				if (seenIndices.add(index)
						&& node.getWeakIRepresentative(index) != storeNode) {
					mNumModuloEdges++;
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("  SecondaryEdge: ["
								+ index + "] "
								+ node + " to " + storeNode);
					}
					node.mergeSecondary(storeNode, store, mPropClauses);
				}
				node = node.mPrimaryEdge;
			}
		}
	}

	/**
	 * Auxiliary class to find the path between two array nodes for
	 * a given store index.
	 *
	 */
	private class Cursor {
		ArrayNode mNode;

		public Cursor(CCTerm term, ArrayNode node) {
			mNode = node;
		}
		
		/**
		 * Collect the store indices from this to destNode over their common root using only the primary edges. The
		 * arrays must be weakly equivalent.
		 * 
		 * @param destNode
		 *            the second array.
		 * @param storeIndices
		 *            a map where the store indices are collected to.
		 */
		public void collectOverPrimaries(ArrayNode destNode, Set<CCTerm> storeIndices) {
			// compute the steps to the common root
			int steps1 = mNode.countPrimaryEdges();
			int steps2 = destNode.countPrimaryEdges();
			// if one needs more step than the other, follow the primary edges until the steps equal
			while (steps1 > steps2) {
				storeIndices.add(getIndexFromStore(mNode.mPrimaryStore));
				mNode = mNode.mPrimaryEdge;
				steps1--;
			}
			while (steps2 > steps1) {
				storeIndices.add(getIndexFromStore(destNode.mPrimaryStore));
				destNode = destNode.mPrimaryEdge;
				steps2--;
			}
			// now follow the primary edge from both nodes until the common ancestor is found
			while (mNode != destNode) {
				storeIndices.add(getIndexFromStore(mNode.mPrimaryStore));
				storeIndices.add(getIndexFromStore(destNode.mPrimaryStore));
				mNode = mNode.mPrimaryEdge;
				destNode = destNode.mPrimaryEdge;
			}
		}

		/**
		 * Collect the store indices on the path from this its weak representative on index using exactly one secondary
		 * edge. It first determines the next secondary edge, collects the primary stores that are needed to reach one
		 * side of it and then the secondary store.
		 * 
		 * @param index
		 *            the select index of the selects whose equality is propagated.
		 * @param storeIndices
		 *            All store indices are added to this map as side-effect.
		 */
		private void collectOneSecondary(CCTerm index, Set<CCTerm> storeIndices) {
			final ArrayNode selectNode = mNode.findSecondaryNode(index);
			final CCAppTerm store = selectNode.mSecondaryStore;
			final CCTerm array = getArrayFromStore(store);
			final ArrayNode arrayNode = mCongRoots.get(array.getRepresentative());
			final ArrayNode storeNode = mCongRoots.get(store.getRepresentative());
			if (arrayNode.findSecondaryNode(index) == selectNode) {
				collectOverPrimaries(arrayNode, storeIndices);
				mNode = storeNode;
			} else {
				assert storeNode.findSecondaryNode(index) == selectNode;
				collectOverPrimaries(storeNode, storeIndices);
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
			int steps1 = mNode.countSecondaryEdges(index);
			int steps2 = dest.mNode.countSecondaryEdges(index);
			while (steps1 > steps2) {
				collectOneSecondary(index, storeIndices);
				steps1--;
			}
			while (steps2 > steps1) {
				dest.collectOneSecondary(index, storeIndices);
				steps2--;
			}
			while (mNode.findSecondaryNode(index) != dest.mNode.findSecondaryNode(index)) {
				collectOneSecondary(index, storeIndices);
				dest.collectOneSecondary(index, storeIndices);
			}
			collectOverPrimaries(dest.mNode, storeIndices);
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
		final ArrayNode node1 = mCongRoots.get(array1.getRepresentative());
		final ArrayNode node2 = mCongRoots.get(array2.getRepresentative());
		final Cursor cursor1 = new Cursor(array1, node1); 
		final Cursor cursor2 = new Cursor(array2, node2); 
		assert index == index.getRepresentative();
		cursor1.collect(index, cursor2, storeIndices);
	}

	private void createPropagatedClauses() {
		for (final ArrayLemma lemma : mPropClauses) {
			final CCTerm lhs = lemma.getEquality().getFirst();
			final CCTerm rhs = lemma.getEquality().getSecond();
			assert lhs.getRepresentative() != rhs.getRepresentative();
			switch (lemma.getRule()) {
			case READ_OVER_WEAKEQ: {
				final CCAppTerm select1 = (CCAppTerm) lhs;
				final CCAppTerm select2 = (CCAppTerm) rhs;
				final CCTerm index1 = getIndexFromSelect(select1);
				final CCTerm array1 = getArrayFromSelect(select1);
				final CCTerm array2 = getArrayFromSelect(select2);
				final Set<CCTerm> storeIndices = new HashSet<CCTerm>();
				computeStoreIndices(index1.getRepresentative(), array1, array2, storeIndices);
				final Set<CCEquality> propClause = new HashSet<CCEquality>();
				for (final CCTerm idx : storeIndices) {
					assert index1.getRepresentative() != idx.getRepresentative();
					final CCEquality lit = CClosure.createEquality(index1, idx);
					if (lit != null) {
						assert lit.getDecideStatus() != lit;
						if (lit.getDecideStatus() == null) {
							propClause.add(lit);
						}
					}
				}
				final CCEquality lit = CClosure.createEquality(select1, select2);
				if (lit != null) {
					assert lit.getDecideStatus() != lit;
					if (lit.getDecideStatus() == null) {
						propClause.add(lit);
					}
				}
				lemma.mUndecidedLits = propClause;
				break;
			}
			case CONST_WEAKEQ: {
				final CCEquality lit = CClosure.createEquality(lhs, rhs);
				assert lit == null || lit.getDecideStatus() != lit;
				final Set<CCEquality> propClause = new HashSet<CCEquality>();
				if (lit != null && lit.getDecideStatus() == null) {
					propClause.add(lit);
				}
				lemma.mUndecidedLits = propClause;
				break;
			}
			case READ_CONST_WEAKEQ: {
				final CCAppTerm select1 = (CCAppTerm) lhs;
				final CCTerm index1 = getIndexFromSelect(select1);
				final CCTerm array1 = getArrayFromSelect(select1);
				final CCTerm array2 = findConst(rhs);
				final Set<CCTerm> storeIndices = new HashSet<CCTerm>();
				computeStoreIndices(index1.getRepresentative(), array1, array2, storeIndices);
				final Set<CCEquality> propClause = new HashSet<CCEquality>();
				for (final CCTerm idx : storeIndices) {
					assert index1.getRepresentative() != idx.getRepresentative();
					final CCEquality lit = CClosure.createEquality(index1, idx);
					if (lit != null) {
						assert lit.getDecideStatus() != lit;
						if (lit.getDecideStatus() == null) {
							propClause.add(lit);
						}
					}
				}
				final CCEquality lit = CClosure.createEquality(lhs, rhs);
				if (lit != null) {
					assert lit.getDecideStatus() != lit;
					if (lit.getDecideStatus() == null) {
						propClause.add(lit);
					}
				}
				lemma.mUndecidedLits = propClause;
				break;
			}
			default:
				throw new AssertionError("Unknown Array Rule: " + lemma.getRule());
			}
		}
	}

	private boolean buildWeakEq() {
		mNumBuildWeakEQ++;
		final long startTime = System.nanoTime();
		mCongRoots = new HashMap<CCTerm, ArrayNode>();
		for (final CCTerm array : mArrays) {
			final CCTerm rep = array.getRepresentative();
			if (!mCongRoots.containsKey(rep)) {
				final ArrayNode node = new ArrayNode(rep);
				node.computeSelects(mSelectFunNum);
				mCongRoots.put(rep, node);
			}
		}
		for (final CCAppTerm term : mConsts) {
			setConst(term);
		}
		for (final CCAppTerm store : mStores) {
			merge(store);
		}

		createPropagatedClauses();

		mTimeBuildWeakEq += (System.nanoTime() - startTime);
		return !mPropClauses.isEmpty();
	}
	
	/**
	 * Make all const terms their own weak representative. This works since we already propagated equalities between
	 * const arrays in the same weak equivalance class.
	 */
	private void makeConstReps() {
		for (CCTerm term : mConsts) {
			ArrayNode node = mCongRoots.get(term.getRepresentative());
			node.makeWeakRepresentative();
		}
	}

	/**
	 * Compute all weakeq-ext instances.
	 * @return <code>true</code> if and only if we found a new instance.
	 */
	private boolean computeWeakeqExt() {
		final long startTime = System.nanoTime();
		makeConstReps();

		/*
		 * makeConstReps ensures that in each weak equivalence class, the const term is the weak representative. So if
		 * mConstTerm != null then primary edge is null and all mSelects must have a value equal to the constant (in
		 * fact mSelects is empty since we removed them).
		 */
		mArrayModels = new HashMap<ArrayNode, Map<CCTerm,Object>>();
		final HashMap<Map<CCTerm,Object>,ArrayNode> inverse = 
				new HashMap<Map<CCTerm,Object>, ArrayNode>();
		final HashSet<SymmetricPair<ArrayNode>> propEqualities = 
				new HashSet<SymmetricPair<ArrayNode>>();
		final ArrayDeque<ArrayNode> todoQueue = 
				new ArrayDeque<ArrayNode>(mCongRoots.values());
		while (!todoQueue.isEmpty()) {
			final ArrayNode node = todoQueue.getFirst();
			if (mArrayModels.containsKey(node)) {
				todoQueue.removeFirst();
				continue;
			}
			if (node.mPrimaryEdge != null && !mArrayModels.containsKey(node.mPrimaryEdge)) {
				todoQueue.addFirst(node.mPrimaryEdge);
				continue;
			}
			todoQueue.removeFirst();
			final HashMap<CCTerm, Object> nodeMapping
				= new HashMap<CCTerm, Object>();
			CCTerm constRep = null;
			ArrayNode weakRep = node.getWeakRepresentative();
			if (weakRep.mConstTerm != null) {
				constRep = getValueFromConst(weakRep.mConstTerm).getRepresentative();
			}
			if (node == weakRep) {
				nodeMapping.put(null, node);
				for (final Entry<CCTerm, CCAppTerm> e : node.mSelects.entrySet()) {
					CCTerm value = e.getValue().getRepresentative();
					assert constRep == null || value == constRep;
					if (value != constRep) {
						nodeMapping.put(e.getKey(), value);
					}
				}
			} else {
				final CCTerm storeIndex = getIndexFromStore(node.mPrimaryStore)
						.getRepresentative();
				nodeMapping.putAll(mArrayModels.get(node.mPrimaryEdge));
				nodeMapping.remove(storeIndex);
				final ArrayNode weakiRep = node.getWeakIRepresentative(storeIndex);
				final CCTerm value = weakiRep.mSelects.get(storeIndex);
				if (value != null) { // NOPMD
					if (value.getRepresentative() != constRep) {
						nodeMapping.put(storeIndex, value.getRepresentative());
					}
				} else if (weakiRep != weakRep) {
					nodeMapping.put(storeIndex, weakiRep);
				}
			}
			mArrayModels.put(node, nodeMapping);
			final ArrayNode prev = inverse.put(nodeMapping, node);
			if (prev != null) {
				propEqualities.add(new SymmetricPair<ArrayNode>(prev, node));
			}
		}
		for (final SymmetricPair<ArrayNode> equalities : propEqualities) {
			mNumInstsEq++;
			final WeakCongruencePath path = new WeakCongruencePath(this);
			final Clause lemma = path.computeWeakeqExt(
					equalities.getFirst().mTerm, equalities.getSecond().mTerm,
					mCClosure.mEngine.isProofGenerationEnabled());
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("AL sw: " + lemma);
			}
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
	
	boolean isConst(CCTerm term) {
		return mConsts.contains(term);
	}

	private void cleanCaches() {
		mCongRoots = null;
		mPropClauses.clear();
	}
}
