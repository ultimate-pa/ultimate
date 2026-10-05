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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedLinkedHashSet;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Array theory solver based on weak equivalence classes. The underlying data structure is explained in our paper
 * "Weakly Equivalent Arrays".
 *
 * <p>
 * The function <code>checkpoint</code> computes the weak equivalent graph and collects the equalities that would appear
 * in the weak lemmas, i.e., the index disequalities and the propagated equality on the select terms. If there is only
 * one equality in a lemma it propagates the lemma. Otherwise, the mere creation of the equality literals, will force
 * the DPLL engine at some point to decide these literals.
 * </p>
 *
 * <p>
 * The produced lemmas will always contain the equalities in a canonical form, namely the propagated equality is on the
 * select terms, for which the equality was propagated and the index disequality is on the index of the first select
 * term with the index of the store term.
 * </p>
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
		 * The ccterm this node corresponds to. This is always the representative, i.e.,
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
		 * A map from index to the selects that exists for this weak-i equivalence class. Used to quickly merge weak-i
		 * classes and to quickly compute new equivalences. We only have to remember one of the select terms for each
		 * index, since the other are supposed to be equal.
		 *
		 * The key is always the value identity (representative and offset-to-representative) of the index of the
		 * corresponding select, i.e. {@link CCParameter#getValueKey()} of {@link #getIndexParamFromSelect}. Two selects
		 * on indices with the same value share a key.
		 *
		 * This is an arbitrary map for weak representative (no primary edge), should be a singleton for weak-i
		 * representatives (primary edge exists, but no secondary edge) and empty for all other nodes (where both edges
		 * exist).
		 */
		Map<CCParameter, CCAppTerm> mSelects;

		CCAppTerm mConstTerm;

		/**
		 * Create a new array term corresponding to a ccterm.
		 *
		 * @param ccterm
		 *            the corresponding ccterm. This must be its own representative.
		 */
		public ArrayNode(final CCTerm ccterm) {
			assert ccterm.isRepresentative();
			mTerm = ccterm;
			mPrimaryEdge = mSecondaryEdge = null;
			mPrimaryStore = null;
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
		public ArrayNode getWeakIRepresentative(CCParameter index) {
			index = index.getValueKey();
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				if (getIndexFromStore(node.mPrimaryStore).getValueKey().equals(index)) {
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
			final CCParameter index = getIndexFromStore(mPrimaryStore).getValueKey();
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
		 * Make this array node the representative of its weak equivalence group by inverting all the store edges.
		 */
		public void makeWeakRepresentative() {
			if (mPrimaryEdge == null) {
				return;
			}
			// hash map from store indices we have seen on the primary path to the previous destination/new source of
			// the primary edge (or in other words, to the new candidate for weak-i equivalence class).
			final LinkedHashMap<CCParameter, ArrayNode> seenStores = new LinkedHashMap<>();
			// for each index, the information about secondary edge that we later need to invert.
			final LinkedHashMap<CCParameter, ArrayNode> todoSecondary = new LinkedHashMap<>();
			final LinkedHashMap<CCParameter, CCAppTerm> todoSecondaryStores = new LinkedHashMap<>();
			// the select information for the new root node.
			final LinkedHashMap<CCParameter, CCAppTerm> newSelectMap = new LinkedHashMap<>();
			ArrayNode node = this;
			ArrayNode prev = null;
			CCAppTerm prevStore = null;
			while (node.mPrimaryEdge != null) {
				// invert the last primary edge
				final ArrayNode next = node.mPrimaryEdge;
				final CCAppTerm nextStore = node.mPrimaryStore;
				node.mPrimaryEdge = prev;
				node.mPrimaryStore = prevStore;

				final CCParameter index = getIndexFromStore(nextStore).getValueKey();
				final ArrayNode old = seenStores.put(index, next);
				if (old == node) {
					// the node is in the middle of two consecutive stores on the same
					// index. There is no need to move the secondary information
					// around.
					//
					// This branch is intentionally left empty!
				} else if (node.mSecondaryEdge != null) { // NOPMD
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
						assert (getIndexFromStore(old.mPrimaryStore).getValueKey().equals(index));
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
			final Map<CCParameter, CCAppTerm> rootSelects = node.mSelects;
			node.mSelects = Collections.emptyMap();
			for (final Entry<CCParameter, ArrayNode> entry : seenStores.entrySet()) {
				// The seen stores get the new representatives of their weak-i equivalence groups
				final CCParameter index = entry.getKey();
				final CCAppTerm select = rootSelects.remove(index);
				if (select != null) {
					entry.getValue().mSelects = Collections.singletonMap(index, select);
				}
			}
			// Now invert the secondary edges
			for (final Entry<CCParameter, ArrayNode> entry : todoSecondary.entrySet()) {
				final CCParameter index = entry.getKey();
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
		public void mergeWith(final ArrayNode storeNode, final CCAppTerm store, final Collection<ArrayLemma> propLemmas) {
			assert mPrimaryEdge == null && storeNode.mPrimaryEdge == null;
			mPrimaryEdge = storeNode;
			mPrimaryStore = store;

			// merge the consts;
			// this map collects all selects in the other class, that may need to be merge with the const.
			final LinkedHashMap<CCParameter, CCAppTerm> mergeConstSelects = new LinkedHashMap<>();
			if (mConstTerm != null) {
				if (storeNode.mConstTerm == null) {
					storeNode.mConstTerm = mConstTerm;
					mConstTerm = null;
					mergeConstSelects.putAll(storeNode.mSelects);
				} else {
					final CCParameter const1 = getValueFromConst(mConstTerm);
					final CCParameter const2 = getValueFromConst(storeNode.mConstTerm);
					if (const1.getRepresentative() != const2.getRepresentative()
							|| !const1.getOffsetToRep().equals(const2.getOffsetToRep())) {
						propLemmas.add(new ArrayLemma(RuleKind.CONST_WEAKEQ, const1, const2));
					}
				}
			} else if (storeNode.mConstTerm != null) {
				mergeConstSelects.putAll(mSelects);
			}
			mergeConstSelects.remove(getIndexFromStore(store).getValueKey());

			// merge the selects;
			Map<CCParameter, CCAppTerm> newSelects = Collections.emptyMap();
			for (final Entry<CCParameter, CCAppTerm> entry : mSelects.entrySet()) {
				final CCParameter index = entry.getKey();
				final CCAppTerm select = entry.getValue();
				assert select != null;
				if (index.equals(getIndexFromStore(store).getValueKey())) {
					newSelects = Collections.singletonMap(index, select);
				} else {
					final CCAppTerm otherSelect = storeNode.mSelects.get(index);
					if (otherSelect == null) {
						// move the select to new representative.
						storeNode.mSelects.put(index, select);
					} else {
						mergeConstSelects.remove(index);
						// Offset-aware: two selects in the same class but at different offsets are NOT already equal —
						// the propagated equality is a (false) offset equality that raises the conflict.
						if (!select.sameValueAs(otherSelect)) {
							// add propagated equality
							propLemmas.add(new ArrayLemma(RuleKind.READ_OVER_WEAKEQ, select, otherSelect));
						}
					}
				}
			}
			mSelects = newSelects;
			if (storeNode.mConstTerm != null) {
				final CCParameter const1 = getValueFromConst(storeNode.mConstTerm);
				final ArrayNode constNode = mCongRoots.get(storeNode.mConstTerm.getRepresentative());
				for (final Entry<CCParameter, CCAppTerm> entry : mergeConstSelects.entrySet()) {
					final CCParameter index = entry.getKey();
					final CCAppTerm select = entry.getValue();
					// check if selected array is weakly equal to the const array
					if (constNode.getWeakIRepresentative(index) == storeNode) {
						// do not keep select, we will merge it with the constant value
						storeNode.mSelects.remove(index);
						// Offset-aware: a select in the same class as the const value but at a different offset is NOT
						// already equal — propagating the (false) offset equality raises the conflict.
						if (!select.sameValueAs(const1)) {
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
		public void mergeSecondary(final ArrayNode storeNode, final CCAppTerm store, final Collection<ArrayLemma> propEqualities) {
			assert storeNode.mPrimaryEdge == null;
			assert mPrimaryEdge != null;
			assert !getIndexFromStore(mPrimaryStore).sameValueAs(getIndexFromStore(store));
			if (mSecondaryEdge != null) {
				makeWeakIRepresentative();
			}
			mSecondaryEdge = storeNode;
			mSecondaryStore = store;
			final CCParameter storeIndex = getIndexFromStore(mPrimaryStore).getValueKey();
			if (!mSelects.isEmpty()) {
				final CCAppTerm select = mSelects.get(storeIndex);
				assert (select != null);
				final CCAppTerm otherSelect = storeNode.mSelects.get(storeIndex);
				if (otherSelect == null) {
					storeNode.mSelects.put(storeIndex, select);
				} else {
					if (!select.sameValueAs(otherSelect)) {
						propEqualities.add(new ArrayLemma(RuleKind.READ_OVER_WEAKEQ, select, otherSelect));
					}
				}
				mSelects = Collections.emptyMap();
			}
			if (storeNode.mConstTerm != null) {
				// We only need to merge a select and const, if the const term is now weak-i equivalent to the store
				// node.
				final ArrayNode constNode = mCongRoots.get(storeNode.mConstTerm.getRepresentative());
				if (constNode.getWeakIRepresentative(storeIndex) == storeNode) {
					// do not keep select, we will merge it with the constant value
					final CCAppTerm select = storeNode.mSelects.remove(storeIndex);
					final CCParameter const1 = getValueFromConst(storeNode.mConstTerm);
					if (select != null && !select.sameValueAs(const1)) {
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
		public int countSecondaryEdges(final CCParameter index) {
			assert index.getValueKey().equals(index);
			int count = 0;
			ArrayNode node = this;
			while (node.mPrimaryEdge != null) {
				if (getIndexFromStore(node.mPrimaryStore).getValueKey().equals(index)) {
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
		public ArrayNode findSecondaryNode(final CCParameter index) {
			assert index.getValueKey().equals(index);
			ArrayNode node = this;
			while (node.mPrimaryEdge != null && !getIndexFromStore(node.mPrimaryStore).getValueKey().equals(index)) {
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
		 * Returns the hash code. This equals the hash code of the underlying ccterm. Note that our algorithm guarantees
		 * that there is at most one ArrayTerm created for any ccterm.
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
		SymmetricPair<CCParameter> mPropagatedEq;
		Set<CCEquality> mUndecidedLits;

		public ArrayLemma(final RuleKind rule, final CCParameter lhs, final CCParameter rhs) {
			mRule = rule;
			mPropagatedEq = new SymmetricPair<>(lhs, rhs);
		}

		public RuleKind getRule() {
			return mRule;
		}

		public SymmetricPair<CCParameter> getEquality() {
			return mPropagatedEq;
		}

		@Override
		public int hashCode() {
			return HashUtils.hashJenkins(mRule.hashCode(), mPropagatedEq);
		}

		@Override
		public boolean equals(final Object other) {
			if (other instanceof ArrayLemma) {
				final ArrayLemma o = (ArrayLemma) other;
				return mRule == o.mRule && mPropagatedEq.equals(o.mPropagatedEq);
			}
			return false;
		}

		@Override
		public String toString() {
			return "ArrayLemma[" + mPropagatedEq + " ; " + mUndecidedLits + "]";
		}
	}

	private final Clausifier mClausifier;
	private final CClosure mCClosure;

	private final ScopedArrayList<CCTerm> mArrays = new ScopedArrayList<>();
	private final ScopedLinkedHashSet<CCAppTerm> mStores = new ScopedLinkedHashSet<>();
	private final ScopedLinkedHashSet<CCAppTerm> mDiffs = new ScopedLinkedHashSet<>();
	private final ScopedLinkedHashSet<CCAppTerm> mConsts = new ScopedLinkedHashSet<>();

	private final ArrayDeque<ArrayLemma> mPropClauses = new ArrayDeque<>();

	private final LogProxy mLogger;

	/**
	 * The push/pop level, i.e., the number of push minus the number of pop
	 * operations.
	 */
	private int mPushPopLevel = 0;
	/**
	 * The first push/pop level which contains an select or store with a quantified
	 * variable as index. This is -1 if there is no such quantifer.
	 */
	private int mNeedDiffIndexLevel = -1;

	/// Cache for the congruence roots;
	Map<CCTerm, ArrayNode> mCongRoots = null;
	/**
	 * The array models store for every array node the index-value map. The indices are all their own representative.
	 * The value is the select cc term representative. If there is no select term for that index, the value is the
	 * weak-i representative node. At index null, the map stores the weak representative node.
	 */
	Map<ArrayNode, Map<CCParameter, Object>> mArrayModels = null;

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

	public ArrayTheory(final Clausifier clausifier, final CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mLogger = mCClosure.getLogger();
	}

	@Override
	public Clause startCheck() {
		cleanCaches();
		return null;
	}

	@Override
	public void endCheck() {
		// Don't clean the caches here. We might need them to build a model!
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		if (literal instanceof CCEquality) {
			cleanCaches();
		} else {
			for (final ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.remove(literal.negate()) && lemma.mUndecidedLits.isEmpty()) {
					return explainPropagation(lemma);
				}
			}
		}
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		cleanCaches();
	}

	@Override
	public Clause checkpoint() {
		if (mCongRoots == null && buildWeakEq()) {
			for (final ArrayLemma lemma : mPropClauses) {
				if (lemma.mUndecidedLits.isEmpty()) {
					return explainPropagation(lemma);
				}
			}
		}
		return null;
	}

	@Override
	public Clause finalCheck() {
		do {
			Clause conflict = mCClosure.checkpoint();
			if (conflict != null) {
				return conflict;
			}
			conflict = checkpoint();
			if (conflict != null) {
				return conflict;
			}
			if (mPropClauses.isEmpty()) {
				final boolean foundLemma = computeWeakeqExt();
				if (foundLemma) {
					mArrayModels = null;
				}
			}
		} while (mCongRoots == null);
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
	public Clause getUnitClause(final Literal literal) {
		assert literal instanceof CCEquality;
		if (mCongRoots == null) {
			buildWeakEq();
		}
		for (final ArrayLemma lemma : mPropClauses) {
			final Set<CCEquality> lits = lemma.mUndecidedLits;
			if (lits.isEmpty() || (lits.size() == 1 && lits.contains(literal))) {
				return explainPropagation(lemma);
			}
		}
		throw new AssertionError("Cannot explain unit literal!");
	}

	@Override
	public int checkCompleteness() {
		return DPLLEngine.COMPLETE;
	}

	private Clause explainPropagation(final ArrayLemma lemma) {
		final SymmetricPair<CCParameter> equality = lemma.getEquality();
		final long start = System.nanoTime();
		mNumInstsSelect++;
		final WeakCongruencePath path = new WeakCongruencePath(this);
		final Clause clause;
		switch (lemma.getRule()) {
		case READ_OVER_WEAKEQ:
			clause = path.computeSelectOverWeakEQ((CCAppTerm) equality.getFirst(), (CCAppTerm) equality.getSecond(),
					mCClosure.isProofGenerationEnabled());
			break;
		case CONST_WEAKEQ:
			clause = path.computeConstOverWeakEQ(findConst(equality.getFirst()), findConst(equality.getSecond()),
					mCClosure.isProofGenerationEnabled());
			break;
		case READ_CONST_WEAKEQ:
			clause = path.computeSelectConstOverWeakEQ((CCAppTerm) equality.getFirst(), findConst(equality.getSecond()),
					mCClosure.isProofGenerationEnabled());
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
		for (final ArrayLemma lemma : mPropClauses) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("AL suggest: " + lemma);
			}
			return lemma.mUndecidedLits.iterator().next();
		}
		return null;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		if (logger.isInfoEnabled()) {
			logger.info("Array: #Arrays: %d, #BuildWeakEQ: %d, #ModEdges: %d, " + "#addStores: %d, #merges: %d",
					mArrays.size(), mNumBuildWeakEQ, mNumModuloEdges, mNumAddStores, mNumMerges);
			logger.info("Insts: ReadOverWeakEQ: %d, WeakeqExt: %d", mNumInstsSelect, mNumInstsEq);
			logger.info("Time: BuildWeakEq: %d.%03d ms, BuildWeakEqi: %d.%03d ms",
					mTimeBuildWeakEq / 1000000, mTimeBuildWeakEq / 1000 % 1000,
					mTimeBuildWeakEqi / 1000000, mTimeBuildWeakEqi / 1000 % 1000);
			logger.info("Time: Propagation %d.%03d ms, Explanations: %d.%03d ms",
					mTimePropagation / 1000000, mTimePropagation / 1000 % 1000,
					mTimeExplanations / 1000000, mTimeExplanations / 1000 % 1000);
		}

	}

	@Override
	public void dumpModel(final LogProxy logger) {
		if (!logger.isInfoEnabled()) {
			return;
		}
		for (final Entry<ArrayNode, Map<CCParameter, Object>> entry : mArrayModels.entrySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(entry.getKey().mTerm).append(" = store[");
			sb.append(entry.getKey().getWeakRepresentative().mTerm);
			for (final Entry<CCParameter, Object> storeEntry : entry.getValue().entrySet()) {
				if (storeEntry.getKey() == null) {
					continue;
				}
				sb.append(",(").append(storeEntry.getKey()).append(":=").append(storeEntry.getValue()).append(')');
			}
			sb.append(']');
			logger.info(sb.toString());
		}
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void backtrackAll() {
		mPropClauses.clear();
	}

	@Override
	public void backtrackStart() {
		mPropClauses.clear();
	}

	@Override
	public Clause backtrackComplete() {
		return null;
	}

	@Override
	public void restart(final int iteration) {
		// Nothing to do
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		// Nothing to do
	}

	@Override
	public void push() {
		mArrays.beginScope();
		mStores.beginScope();
		mConsts.beginScope();
		mDiffs.beginScope();
		mPushPopLevel++;
	}

	@Override
	public void pop() {
		if (mNeedDiffIndexLevel == mPushPopLevel) {
			// no longer need diff for quantified arrays
			mNeedDiffIndexLevel = -1;
		}
		mPushPopLevel--;
		mArrays.endScope();
		mStores.endScope();
		mConsts.endScope();
		mDiffs.endScope();
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":Array",
				new Object[][] { { "NumArrays", mArrays.size() }, { "BuildWeakEQ", mNumBuildWeakEQ },
						{ "AddStores", mNumAddStores }, { "Merges", mNumMerges }, { "ModuloEdges", mNumModuloEdges },
						{ "ReadOverWeakeq", mNumInstsSelect }, { "WeakeqExt", mNumInstsEq },
						{ "Times",
								new Object[][] { { "BuildWeakEq", mTimeBuildWeakEq },
										{ "BuildWeakEqi", mTimeBuildWeakEqi }, { "Propagation", mTimePropagation },
										{ "Explanations", mTimeExplanations } } } } };
	}

	public void fillInModel(final ModelBuilder builder, final List<CCTerm> ccArrayTerms) {
		assert mArrayModels != null;
		final Sort arraySort = ccArrayTerms.get(0).getFlatTerm().getSort();
		assert arraySort.isArraySort();
		final Sort valueSort = arraySort.getArguments()[1];
		final Model model = builder.getModel();
		final Theory t = builder.getTheory();
		final ArraySortInterpretation arraySortInterpretation = (ArraySortInterpretation) model
				.provideSortInterpretation(arraySort);
		final List<ArrayNode> arraysTerms = new ArrayList<>(ccArrayTerms.size());
		for (final CCTerm ccterm : ccArrayTerms) {
			arraysTerms.add(mCongRoots.get(ccterm));
		}
		final ArrayDeque<ArrayNode> todoQueue = new ArrayDeque<>(arraysTerms);
		while (!todoQueue.isEmpty()) {
			final ArrayNode node = todoQueue.removeFirst();
			if (builder.getModelValue(node.mTerm) != null) {
				// we already did that term
				continue;
			}
			final ArrayNode parent = node.mPrimaryEdge;
			if (parent == null) {
				// Note that constant arrays are the representatives, so either this is a
				// constant array or
				// it's not weakly equivalent to one.
				if (node.mConstTerm != null) {
					// getModelValue shifts the representative's value by the const value's offset; using
					// getRepresentative() would drop the offset and build a wrong model value.
					final Term nodeValue = t.term(SMTLIBConstants.CONST, null, arraySort,
							builder.getModelValue(getValueFromConst(node.mConstTerm)));
					builder.setModelValue(node.mTerm, nodeValue);
				} else {
					Term nodeValue;
					if (hasFiniteIndexSort(node.mTerm.getFlatTerm().getSort())) {
						// the array is based on a certain const value, see computeWeakEqExt()
						final Term valueTerm;
						if (hasFiniteElemSort(node.mTerm.getFlatTerm().getSort())) {
							final CCParameter value = (CCParameter) mArrayModels.get(node).get(null);
							valueTerm = builder.getModelValue(value);
						} else {
							valueTerm = model.extendFresh(valueSort);
						}
						nodeValue = t.term(SMTLIBConstants.CONST, null, arraySort, valueTerm);
					} else {
						// this is not a weakly related to a constant array. Use some fresh array.
						nodeValue = model.extendFresh(arraySort);
					}
					// change all indices to the right select value
					for (final Entry<CCParameter, CCAppTerm> indexValuePairs : node.mSelects.entrySet()) {
						final CCParameter index = indexValuePairs.getKey();
						// value identity (getValueKey), so a select whose value sits at a non-zero offset from its
						// representative renders the shifted value, not the representative's.
						final CCParameter value = indexValuePairs.getValue().getValueKey();
						nodeValue = t.term("store", nodeValue, builder.getModelValue(index),
								builder.getModelValue(value));
					}
					// we also need to change the indices we store in the same weak-equivalence
					// class, so that
					// they don't accidentally match the default value.
					for (final ArrayNode other : arraysTerms) {
						if (other.getWeakRepresentative() != node || other == node || other.mSelects.isEmpty()
								|| other.mSecondaryEdge != null) {
							continue;
						}
						assert other.mSelects.size() == 1;
						final CCParameter index = other.mSelects.keySet().iterator().next();
						if (!node.mSelects.containsKey(index)) {
							// we have another array in the weak-equivalence class that may by accident
							// store the
							// default value. To make sure it doesn't equal node, we change the node value
							// at
							// this index to a fresh value
							final Term freshValue = model.extendFresh(valueSort);
							nodeValue = t.term("store", nodeValue, builder.getModelValue(index), freshValue);
						}
					}
					nodeValue = arraySortInterpretation.normalizeStoreTerm(nodeValue);
					builder.setModelValue(node.mTerm, nodeValue);
				}
			} else {
				final Term parentTerm = builder.getModelValue(parent.mTerm);
				if (parentTerm == null) {
					// parent wasn't visited yet; it must be visited first
					// enqueue the node again and its parent.
					todoQueue.addFirst(node);
					todoQueue.addFirst(parent);
					continue;
				}
				final Term secondParentTerm;
				if (node.mSecondaryEdge != null) {
					secondParentTerm = builder.getModelValue(node.mSecondaryEdge.mTerm);
					if (secondParentTerm == null) {
						// secondary parent wasn't visited yet; it must be visited first
						// enqueue the node again and its parent.
						todoQueue.addFirst(node);
						todoQueue.addFirst(node.mSecondaryEdge);
						continue;
					}
				} else {
					secondParentTerm = null;
				}
				final CCParameter ccIndex = getIndexFromStore(node.mPrimaryStore).getValueKey();
				final CCAppTerm ccValue = node.mSelects.get(ccIndex);
				final Term index = builder.getModelValue(ccIndex);
				final Term value = secondParentTerm != null ? arraySortInterpretation.getSelect(secondParentTerm, index)
						: ccValue == null ? model.extendFresh(valueSort) : builder.getModelValue(ccValue.getValueKey());
				Term nodeValue = t.term("store", parentTerm, index, value);
				nodeValue = arraySortInterpretation.normalizeStoreTerm(nodeValue);
				builder.setModelValue(node.mTerm, nodeValue);
			}
		}
	}

	public void notifyArray(final CCTerm array, final boolean isStore, final boolean isConst) {
		if (isStore) {
			mStores.add((CCAppTerm) array);
			mNumAddStores++;
		}
		if (isConst) {
			mConsts.add((CCAppTerm) array);
		}
		mArrays.add(array);
		cleanCaches();
	}

	public void notifyDiff(final CCAppTerm diff) {
		mDiffs.add(diff);
	}

	public static boolean isSelectTerm(final CCParameter term) {
		if (term instanceof CCAppTerm) {
			return ((CCAppTerm) term).getFunctionSymbol().getName().equals(SMTLIBConstants.SELECT);
		}
		return false;
	}

	public static boolean isStoreTerm(final CCParameter term) {
		if (term instanceof CCAppTerm) {
			return ((CCAppTerm) term).getFunctionSymbol().getName().equals(SMTLIBConstants.STORE);
		}
		return false;
	}

	public static boolean isConstTerm(final CCParameter term) {
		if (term instanceof CCAppTerm) {
			return ((CCAppTerm) term).getFunctionSymbol().getName().equals(SMTLIBConstants.CONST);
		}
		return false;
	}

	public static boolean isDiffTerm(final CCParameter term) {
		if (term instanceof CCAppTerm) {
			return ((CCAppTerm) term).getFunctionSymbol().getName().equals(SMTInterpolConstants.DIFF);
		}
		return false;
	}

	public static CCTerm getArrayFromSelect(final CCAppTerm select) {
		assert isSelectTerm(select);
		// the array argument is never numeric; the cast asserts it carries no offset
		return (CCTerm) select.getArgParam(0);
	}

	/**
	 * The value of the index of a select term as a {@link CCParameter}, i.e. argument 1 together with its structural
	 * offset. With offset equalities the index of {@code (select a (+ i 5))} is the CCTerm {@code i} plus offset 5.
	 */
	public static CCParameter getIndexFromSelect(final CCAppTerm select) {
		assert isSelectTerm(select);
		return select.getArgParam(1);
	}

	public static CCTerm getArrayFromStore(final CCAppTerm store) {
		assert isStoreTerm(store);
		// the array argument is never numeric; the cast asserts it carries no offset
		return (CCTerm) store.getArgParam(0);
	}

	/**
	 * The value of the index of a store term as a {@link CCParameter}, i.e. argument 1 together with its structural
	 * offset (see {@link #getIndexFromSelect}).
	 */
	public static CCParameter getIndexFromStore(final CCAppTerm store) {
		assert isStoreTerm(store);
		return store.getArgParam(1);
	}

	public static CCParameter getValueFromStore(final CCAppTerm store) {
		assert isStoreTerm(store);
		return store.getArgParam(2);
	}

	public static CCParameter getValueFromConst(final CCAppTerm constArr) {
		assert isConstTerm(constArr);
		return constArr.getArgParam(0);
	}

	public static CCTerm getLeftFromDiff(final CCAppTerm diff) {
		assert isDiffTerm(diff);
		// diff arguments are arrays, never numeric; the cast asserts they carry no offset
		return (CCTerm) diff.getArgParam(0);
	}

	public static CCTerm getRightFromDiff(final CCAppTerm diff) {
		assert isDiffTerm(diff);
		// diff arguments are arrays, never numeric; the cast asserts they carry no offset
		return (CCTerm) diff.getArgParam(1);
	}

	public static Sort getArraySortFromSelect(final CCAppTerm select) {
		assert isSelectTerm(select);
		return select.getFunctionSymbol().getParameterSorts()[0];
	}

	public static Sort getArraySortFromStore(final CCAppTerm store) {
		assert isStoreTerm(store);
		return store.getFunctionSymbol().getParameterSorts()[0];
	}

	CCAppTerm findConst(final CCParameter value) {
		for (final CCAppTerm constTerm : mConsts) {
			if (value.equals(getValueFromConst(constTerm))) {
				return constTerm;
			}
		}
		throw new AssertionError("Constant term not found for " + value);
	}

	private void setConst(final CCAppTerm term) {
		final CCParameter const1 = getValueFromConst(term);
		final CCTerm rep = term.getRepresentative();
		final ArrayNode node = mCongRoots.get(rep);
		if (node.mConstTerm != null) {
			final CCParameter const2 = getValueFromConst(node.mConstTerm);
			if (!const1.sameValueAs(const2)) {
				mPropClauses.add(new ArrayLemma(RuleKind.CONST_WEAKEQ, const1, const2));
			}
		} else {
			node.mConstTerm = term;
			for (final CCAppTerm select : node.mSelects.values()) {
				if (!select.sameValueAs(const1)) {
					mPropClauses.add(new ArrayLemma(RuleKind.READ_CONST_WEAKEQ, select, const1));
				}
			}
		}
	}

	private void merge(final CCAppTerm store) {
		final CCTerm array = getArrayFromStore(store);
		final ArrayNode arrayNode = mCongRoots.get(array.getRepresentative());
		final ArrayNode storeNode = mCongRoots.get(store.getRepresentative());
		if (arrayNode == storeNode) {
			return;
		}

		mNumMerges++;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(
					"Merge: [" + getIndexFromStore(store).getValueKey() + "] " + arrayNode + " and " + storeNode);
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

			final HashSet<CCParameter> seenIndices = new HashSet<>();
			final CCParameter storeIndex = getIndexFromStore(store).getValueKey();
			seenIndices.add(storeIndex);
			ArrayNode node = arrayNode;
			while (node.mPrimaryEdge != null) {
				final CCParameter index = getIndexFromStore(node.mPrimaryStore).getValueKey();
				/*
				 * add the index to the seen indices and merge weak-i equivalence classes if index was not seen before
				 * and they are not already the same.
				 */
				if (seenIndices.add(index) && node.getWeakIRepresentative(index) != storeNode) {
					mNumModuloEdges++;
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("  SecondaryEdge: [" + index + "] " + node + " to " + storeNode);
					}
					node.mergeSecondary(storeNode, store, mPropClauses);
				}
				node = node.mPrimaryEdge;
			}
		}
	}

	/**
	 * Auxiliary class to find the path between two array nodes for a given store index.
	 *
	 */
	private class Cursor {
		ArrayNode mNode;

		public Cursor(final CCTerm term, final ArrayNode node) {
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
		public void collectOverPrimaries(ArrayNode destNode, final Set<CCParameter> storeIndices) {
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
		private void collectOneSecondary(final CCParameter index, final Set<CCParameter> storeIndices) {
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
		 * Collect the store indices on the path from this to dest using only indices different from index.
		 *
		 * @param index
		 *            the select index of the selects whose equality is propagated.
		 * @param dest
		 *            the cursor for the second array.
		 * @param storeIndices
		 *            initially an empty map. All store indices are added to this map as side-effect.
		 */
		public void collect(final CCParameter index, final Cursor dest, final Set<CCParameter> storeIndices) {
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
	 * Collect the store indices on the path from array1 to array2 using only indices different from index.
	 *
	 * @param index
	 *            the select index of the selects whose equality is propagated.
	 * @param array1
	 *            the first array.
	 * @param array2
	 *            the second array.
	 * @param storeIndices
	 *            initially an empty map. All store indices are added to this map as side-effect.
	 */
	private void computeStoreIndices(final CCParameter index, final CCTerm array1, final CCTerm array2, final Set<CCParameter> storeIndices) {
		final ArrayNode node1 = mCongRoots.get(array1.getRepresentative());
		final ArrayNode node2 = mCongRoots.get(array2.getRepresentative());
		final Cursor cursor1 = new Cursor(array1, node1);
		final Cursor cursor2 = new Cursor(array2, node2);
		assert index.getValueKey().equals(index);
		cursor1.collect(index, cursor2, storeIndices);
	}

	/**
	 * Create the equality literal expressing that the two index values are equal, i.e.
	 * {@code value(index) == value(storeIndex)}. With offsets this is the offset equality
	 * {@code index.ccTerm == storeIndex.ccTerm + (storeIndex.offset - index.offset)}. If both share the same underlying
	 * CCTerm but differ by a constant the equality is unsatisfiable, so no literal is created (returns {@code null}); the
	 * disjunct it would contribute is always false and can be dropped from the array lemma.
	 */
	private CCEquality createIndexEquality(final CCParameter index, final CCParameter storeIndex) {
		return getCClosure().createEquality(index, storeIndex, false);
	}

	private void createPropagatedClauses() {
		for (final ArrayLemma lemma : mPropClauses) {
			final CCParameter lhs = lemma.getEquality().getFirst();
			final CCParameter rhs = lemma.getEquality().getSecond();
			assert !lhs.sameValueAs(rhs);
			switch (lemma.getRule()) {
			case READ_OVER_WEAKEQ: {
				final CCAppTerm select1 = (CCAppTerm) lhs;
				final CCAppTerm select2 = (CCAppTerm) rhs;
				final CCParameter index1 = getIndexFromSelect(select1);
				final CCTerm array1 = getArrayFromSelect(select1);
				final CCTerm array2 = getArrayFromSelect(select2);
				final Set<CCParameter> storeIndices = new LinkedHashSet<>();
				computeStoreIndices(index1.getValueKey(), array1, array2, storeIndices);
				final Set<CCEquality> propClause = new LinkedHashSet<>();
				for (final CCParameter idx : storeIndices) {
					assert !index1.sameValueAs(idx);
					final CCEquality lit = createIndexEquality(index1, idx);
					if (lit != null) {
						assert lit.getDecideStatus() != lit;
						if (lit.getDecideStatus() == null) {
							propClause.add(lit);
						}
					}
				}
				final CCEquality lit = getCClosure().createEquality(select1, select2, false);
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
				final CCEquality lit = getCClosure().createEquality(lhs, rhs, false);
				assert lit == null || lit.getDecideStatus() != lit;
				final Set<CCEquality> propClause = new LinkedHashSet<>();
				if (lit != null && lit.getDecideStatus() == null) {
					propClause.add(lit);
				}
				lemma.mUndecidedLits = propClause;
				break;
			}
			case READ_CONST_WEAKEQ: {
				final CCAppTerm select1 = (CCAppTerm) lhs;
				final CCParameter index1 = getIndexFromSelect(select1);
				final CCTerm array1 = getArrayFromSelect(select1);
				final CCTerm array2 = findConst(rhs);
				final Set<CCParameter> storeIndices = new LinkedHashSet<>();
				computeStoreIndices(index1.getValueKey(), array1, array2, storeIndices);
				final Set<CCEquality> propClause = new LinkedHashSet<>();
				for (final CCParameter idx : storeIndices) {
					assert !index1.sameValueAs(idx);
					final CCEquality lit = createIndexEquality(index1, idx);
					if (lit != null) {
						assert lit.getDecideStatus() != lit;
						if (lit.getDecideStatus() == null) {
							propClause.add(lit);
						}
					}
				}
				final CCEquality lit = getCClosure().createEquality(lhs, rhs, false);
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

	/**
	 * Fill the select information for the current node. This needs to be called when a new array node is created.
	 * It finds all select applications using the ccterm information and adds them to the mSelects hash map.
	 */
	private void collectSelects(Sort arraySort) {
		final Sort indexSort = arraySort.getArguments()[0];
		final FunctionSymbol selectFsym = arraySort.getTheory().getFunction(SMTLIBConstants.SELECT, arraySort, indexSort);
		for (final CCTerm select : mCClosure.getAllFuncApps(selectFsym)) {
			final CCAppTerm selectApp = (CCAppTerm) select;
			final CCTerm array = getArrayFromSelect(selectApp);
			final ArrayNode node = mCongRoots.get(array.getRepresentative());
			node.mSelects.put(getIndexFromSelect(selectApp).getValueKey(), selectApp);
		}
	}



	private boolean buildWeakEq() {
		mNumBuildWeakEQ++;
		final long startTime = System.nanoTime();
		final HashSet<Sort> arraySorts = new HashSet<>();
		mCongRoots = new LinkedHashMap<>();
		for (final CCTerm array : mArrays) {
			final CCTerm rep = array.getRepresentative();
			if (!mCongRoots.containsKey(rep)) {
				final ArrayNode node = new ArrayNode(rep);
				node.mSelects = new LinkedHashMap<>();
				mCongRoots.put(rep, node);
				arraySorts.add(array.getFlatTerm().getSort());
			}
		}
		for (final Sort arraySort : arraySorts) {
			collectSelects(arraySort);
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
		for (final CCTerm term : mConsts) {
			final ArrayNode node = mCongRoots.get(term.getRepresentative());
			node.makeWeakRepresentative();
		}
	}

	/**
	 * Compute all weakeq-ext instances.
	 *
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
		mArrayModels = new LinkedHashMap<>();
		final HashMap<Sort, CCParameter> defaultValue = new HashMap<>();
		final HashMap<Sort, HashMap<Map<CCParameter, Object>, ArrayNode>> inverse = new HashMap<>();
		final HashSet<SymmetricPair<ArrayNode>> propEqualities = new LinkedHashSet<>();
		final ArrayDeque<ArrayNode> todoQueue = new ArrayDeque<>(mCongRoots.values());
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
			final Sort arraySort = node.mTerm.getFlatTerm().getSort();
			todoQueue.removeFirst();
			final HashMap<CCParameter, Object> nodeMapping = new LinkedHashMap<>();
			final ArrayNode weakRep = node.getWeakRepresentative();
			if (node == weakRep) {
				// The element values stored in the fingerprint are value identities (getValueKey = representative +
				// offsetToRep), not bare representatives: two arrays whose elements agree up to a constant offset must
				// NOT get the same fingerprint, or weakeq-ext would propagate a spurious array equality (e.g.
				// store(c,i,y) vs store(c,i,y+1)). Comparisons against constRep therefore use equals(), not ==.
				CCParameter constRep = null;
				if (weakRep.mConstTerm != null) {
					constRep = getValueFromConst(weakRep.mConstTerm).getValueKey();
					nodeMapping.put(null, constRep);
				} else if (hasFiniteIndexSort(arraySort)) {
					// For finite index sorts we cannot just assume that non weak-equivalent arrays
					// are different. Instead we start all arrays with the same const value. If the
					// element sort is also finite, we need to choose a value from the domain, and
					// we choose some select term. If the element sort is infinite, we choose a
					// fresh value for the array.
					if (hasFiniteElemSort(arraySort)) {
						constRep = defaultValue.get(arraySort);
						if (constRep == null) {
							// we set the constRep to the first select term. If there is no select term, we
							// create one.
							if (weakRep.mSelects.isEmpty()) {
								// just create the (select a (diff a a)) term
								final Term array = weakRep.mTerm.getFlatTerm();
								final Theory theory = array.getTheory();
								final Term diffTerm = theory.term(SMTInterpolConstants.DIFF, array, array);
								final Term selectTerm = theory.term(SMTLIBConstants.SELECT, array, diffTerm);
								mClausifier.addTermAxioms(selectTerm, new SourceAnnotation("", null));
								cleanCaches();
								return true;
							}
							constRep = weakRep.mSelects.values().iterator().next().getValueKey();
							defaultValue.put(arraySort, constRep);
						}
						nodeMapping.put(null, constRep);
					} else {
						nodeMapping.put(null, node.mTerm.mFlatTerm.getSort());
					}
				} else if (mNeedDiffIndexLevel >= 0) {
					// If we have quantified array indices, we need to handle extensionality for
					// arrays that are not weakly equivalent. Unless the arrays have different
					// sorts. So we cannot just assume they are different if they are in different
					// weak equality classes.
					nodeMapping.put(null, node.mTerm.mFlatTerm.getSort());
				} else {
					nodeMapping.put(null, node);
				}
				for (final Entry<CCParameter, CCAppTerm> e : node.mSelects.entrySet()) {
					final CCParameter value = e.getValue().getValueKey();
					if (!value.equals(constRep)) {
						nodeMapping.put(e.getKey(), value);
					}
				}
			} else {
				final CCParameter storeIndex = getIndexFromStore(node.mPrimaryStore).getValueKey();
				nodeMapping.putAll(mArrayModels.get(node.mPrimaryEdge));
				final Object constRep = nodeMapping.get(null);
				nodeMapping.remove(storeIndex);
				final ArrayNode weakiRep = node.getWeakIRepresentative(storeIndex);
				final CCAppTerm valueSelect = weakiRep.mSelects.get(storeIndex);
				if (valueSelect != null) { // NOPMD
					final CCParameter value = valueSelect.getValueKey();
					if (!value.equals(constRep)) {
						nodeMapping.put(storeIndex, value);
					}
				} else if (weakiRep != weakRep) {
					nodeMapping.put(storeIndex, weakiRep);
				}
			}
			mArrayModels.put(node, nodeMapping);
			final ArrayNode prev = inverse.computeIfAbsent(arraySort, s -> new HashMap<>()).put(nodeMapping, node);
			if (prev != null) {
				propEqualities.add(new SymmetricPair<>(prev, node));
			}
		}
		for (final SymmetricPair<ArrayNode> equalities : propEqualities) {
			if (equalities.getFirst().getWeakRepresentative() == equalities.getSecond().getWeakRepresentative()) {
				mNumInstsEq++;
				final WeakCongruencePath path = new WeakCongruencePath(this);
				final Clause lemma = path.computeWeakeqExt(equalities.getFirst().mTerm, equalities.getSecond().mTerm,
						mCClosure.isProofGenerationEnabled());
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("AL sw: " + lemma);
				}
				mCClosure.getEngine().learnClause(lemma);
			}
		}
		for (final SymmetricPair<ArrayNode> equalities : propEqualities) {
			if (equalities.getFirst().getWeakRepresentative() != equalities.getSecond().getWeakRepresentative()) {
				assert mNeedDiffIndexLevel >= 0
						|| hasFiniteIndexSort(equalities.getFirst().mTerm.getFlatTerm().getSort());
				// just create a diff term and let the solver do the rest.
				final Term diffTerm = mClausifier.getTheory().term(SMTInterpolConstants.DIFF,
						equalities.getFirst().mTerm.getFlatTerm(), equalities.getSecond().mTerm.getFlatTerm());
				mClausifier.addTermAxioms(diffTerm, new SourceAnnotation("", null));
			}
		}
		mTimeBuildWeakEqi += (System.nanoTime() - startTime);
		return !propEqualities.isEmpty();
	}

	private boolean hasFiniteIndexSort(Sort sort) {
		assert sort.isArraySort();
		assert sort.getArguments().length == 2;
		final Sort indexSort = sort.getArguments()[0];
		return !mClausifier.isStablyInfinite(indexSort);
	}

	private boolean hasFiniteElemSort(Sort sort) {
		assert sort.isArraySort();
		assert sort.getArguments().length == 2;
		final Sort indexSort = sort.getArguments()[1];
		return !mClausifier.isStablyInfinite(indexSort);
	}

	CClosure getCClosure() {
		return mCClosure;
	}

	Clausifier getClausifier() {
		return mClausifier;
	}

	public void cleanCaches() {
		mCongRoots = null;
		mPropClauses.clear();
	}

	public CCTerm getWeakRep(final CCTerm array) {
		assert array != null && array.getFlatTerm().getSort().isArraySort();
		if (mCongRoots == null) {
			buildWeakEq();
		}
		final ArrayNode weakRep = mCongRoots.get(array.getRepresentative()).getWeakRepresentative();
		assert weakRep != null;
		return weakRep.mTerm;
	}

	/**
	 * This is called by the quantifier theory to indicate that there is a
	 * quantified variable as a select index or store index. If this is the case, we
	 * need to create diff terms to ensure extensionality is handled correctly.
	 */
	public void setNeedDiffIndices() {
		if (mNeedDiffIndexLevel < 0) {
			mNeedDiffIndexLevel = mPushPopLevel;
		}
	}
}
