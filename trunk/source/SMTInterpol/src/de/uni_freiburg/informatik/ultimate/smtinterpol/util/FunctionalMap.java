/*
 * Copyright (C) 2009-2021 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * This class implements a functional unmodifiable map in form of a tree. It
 * sorts the entries by hash code. Search and balancing degenerates if several
 * items with the same hash code are inserted. This class assumes that computing
 * hash codes is fast (or cached by the key object).
 *
 * Every node stores one key value pair. The nodes on the left are guaranteed to
 * have a smaller hash code, the nodes on the right have a larger or the same
 * hash code.
 *
 * Balancing is done with 2-3 B*-trees. In a two node the left and right
 * children have the same height, in a three node, the right children is one
 * level deeper and doesn't count to the height of the node. In other words the
 * right is a sibling for three nodes.
 *
 * @author Jochen Hoenicke
 *
 * @param <K> Key sort.
 * @param <V> Value sort.
 */
public class FunctionalMap<K, V> extends AbstractMap<K, V> implements Map.Entry<K, V> {
	private static FunctionalMap<?, ?> EMPTY = new FunctionalMap<>();
	FunctionalMap<K, V> mLeft;
	FunctionalMap<K, V> mRight;
	K mKey;
	V mValue;

	@SuppressWarnings("unchecked")
	public static <K, V> FunctionalMap<K, V> empty() {
		return (FunctionalMap<K, V>) EMPTY;
	}

	/**
	 * This encodes size and color in a single field. Positive for black nodes,
	 * negative for red nodes.
	 */
	int mSizeColor;

	/**
	 * Constructor for empty node. Do not call for other purposes.
	 */
	private FunctionalMap() {
		mLeft = null;
		mRight = null;
		mKey = null;
		mValue = null;
		mSizeColor = 0;
	}

	/**
	 * Constructor with given size/color field.
	 *
	 * @param left      the left child.
	 * @param right     the right child.
	 * @param key       the node's key.
	 * @param value     the key's value.
	 * @param sizeColor the node's size, positive if two node, negative for three
	 *                  node.
	 */
	private FunctionalMap(final FunctionalMap<K, V> left, final FunctionalMap<K, V> right, final K key, final V value,
			final int sizeColor) {
		mLeft = left;
		mRight = right;
		mKey = key;
		mValue = value;
		mSizeColor = sizeColor;
		assert left != null && right != null;
		assert key != null && value != null;
		assert isTwoNode() || right.isTwoNode();
		assert size() == left.size() + right.size() + 1;
		assert mRight.getHeight() == getHeight() - (isTwoNode() ? 1 : 0);
	}

	/**
	 * Constructor that computes size automatically.
	 *
	 * @param left      the left child.
	 * @param right     the right child.
	 * @param key       the node's key.
	 * @param value     the key's value.
	 * @param isTwoNode true, if this is a two node.
	 */
	private FunctionalMap(final FunctionalMap<K, V> left, final FunctionalMap<K, V> right, final K key, final V value,
			final boolean isTwoNode) {
		mLeft = left;
		mRight = right;
		mKey = key;
		mValue = value;
		final int size = left.size() + right.size() + 1;
		mSizeColor = isTwoNode ? size : -size;
		assert isTwoNode() || right.isTwoNode();
		assert (left == null && right == null) || (key != null && value != null);
		assert (left == null && right == null) || mRight.getHeight() == getHeight() - (isTwoNode() ? 1 : 0);
	}

	@Override
	public boolean containsKey(final Object key) {
		return get(key) != null;
	}

	@Override
	public V get(final Object key) {
		final int hash = key.hashCode();
		FunctionalMap<K, V> tree = this;
		while (tree != EMPTY) {
			if (hash < tree.mKey.hashCode()) {
				tree = tree.mLeft;
			} else {
				if (hash == tree.mKey.hashCode()) {
					if (tree.mKey.equals(key)) {
						return tree.mValue;
					}
					final V leftValue = tree.mLeft.get(key);
					if (leftValue != null) {
						return leftValue;
					}
				}
				tree = tree.mRight;
			}
		}
		return null;
	}

	public FunctionalMap<K, V> insert(final K key, final V value) {
		final int hash = key.hashCode();
		FunctionalMap<K, V> tree = this;
		// first find position to insert key and remember the path we took.
		final ArrayDeque<FunctionalMap<K, V>> pathFromRoot = new ArrayDeque<>();
		boolean wentLeft = false;
		while (tree != EMPTY) {
			pathFromRoot.add(tree);
			if (hash < tree.mKey.hashCode()) {
				tree = tree.mLeft;
				wentLeft = true;
			} else {
				tree = tree.mRight;
				wentLeft = false;
			}
		}
		// now insert the key
		FunctionalMap<K, V> newNode = new FunctionalMap<>(empty(), empty(), key, value, 1);
		boolean increaseHeight = true;
		while (!pathFromRoot.isEmpty()) {
			FunctionalMap<K, V> parent = pathFromRoot.removeLast();
			if (!increaseHeight) {
				// only update size and child pointer
				newNode = new FunctionalMap<>(
					wentLeft ?  newNode : parent.mLeft,
					wentLeft ? parent.mRight : newNode,
					parent.mKey, parent.mValue,
					parent.mSizeColor < 0 ? parent.mSizeColor - 1 : parent.mSizeColor + 1);
			} else {
				FunctionalMap<K,V> realParent = parent;

				// check if parent has enough space to add
				boolean parentFull = !parent.isTwoNode();
				if (!parentFull && !pathFromRoot.isEmpty()) {
					final FunctionalMap<K,V> grandParent = pathFromRoot.getLast();
					if (!grandParent.isTwoNode() && grandParent.mRight == parent) {
						parentFull = true;
						realParent = pathFromRoot.removeLast();
					}
				}
				if (parentFull) {
					// we now have three keys in realParent, realParent.mRight, newNode.
					// find the middle one.
					if (parent == realParent) {
						// realParent == parent is the middle one, replace left child and continue inserting.
						newNode = new FunctionalMap<>(newNode, realParent.mRight, realParent.mKey, realParent.mValue, true);
					} else if (wentLeft) {
						// newNode is the middle one, but we need to update both children.
						final FunctionalMap<K,V> newLeft = new FunctionalMap<>(realParent.mLeft, newNode.mLeft, realParent.mKey, realParent.mValue, true);
						final FunctionalMap<K,V> newRight = new FunctionalMap<>(newNode.mRight, parent.mRight, parent.mKey, parent.mValue, true);
						newNode = new FunctionalMap<>(newLeft, newRight, newNode.mKey, newNode.mValue, true);
					} else {
						// parent is the middle one, rotate left. Then replace right child.
						final FunctionalMap<K,V> newLeft = new FunctionalMap<>(realParent.mLeft, parent.mLeft, realParent.mKey, realParent.mValue, true);
						newNode = new FunctionalMap<>(newLeft, newNode, parent.mKey, parent.mValue, true);
					}
					parent = realParent;
				} else {
					// we have enough space, stop increasing height.
					increaseHeight = false;
					if (wentLeft) {
						// newNode will be the new parent
						final FunctionalMap<K, V> newRight = new FunctionalMap<>(newNode.mRight, parent.mRight,
								parent.mKey, parent.mValue, true);
						newNode = new FunctionalMap<>(newNode.mLeft, newRight, newNode.mKey, newNode.mValue, false);
					} else {
						// parent will be the new realparent
						newNode = new FunctionalMap<>(parent.mLeft, newNode, parent.mKey, parent.mValue, false);
					}
				}
			}
			if (!pathFromRoot.isEmpty()) {
				wentLeft = pathFromRoot.getLast().mLeft == parent;
			}
		}
		return newNode;
	}

	public FunctionalMap<K, V> delete(final K key) {
		final int hash = key.hashCode();
		FunctionalMap<K, V> tree = this;
		// first find position to insert key and remember the path we took.
		final ArrayList<FunctionalMap<K, V>> pathFromRoot = new ArrayList<>();
		final BitSet wentLeftBits = new BitSet();
		while (tree != EMPTY) {
			boolean wentLeft;
			pathFromRoot.add(tree);
			if (hash < tree.mKey.hashCode()) {
				tree = tree.mLeft;
				wentLeft = true;
			} else if (hash == tree.mKey.hashCode()) {
				if (key.equals(tree.mKey)) {
					break;
				}
				if (tree.mLeft.get(key) != null) {
					tree = tree.mLeft;
					wentLeft = true;
				} else {
					tree = tree.mRight;
					wentLeft = false;
				}
			} else {
				tree = tree.mRight;
				wentLeft = false;
			}
			wentLeftBits.set(pathFromRoot.size() - 1, wentLeft);
		}
		if (tree == EMPTY) {
			return this;
		}
		// now remove the key
		FunctionalMap<K, V> newNode;
		boolean decreaseHeight;
		if (tree.mLeft == EMPTY) {
			pathFromRoot.remove(pathFromRoot.size() - 1);
			newNode = tree.mRight;
			assert (newNode == EMPTY) == tree.isTwoNode();
			decreaseHeight = tree.isTwoNode();
		} else {
			final int removeHeight = pathFromRoot.size() - 1;
			final FunctionalMap<K,V> removeTree = tree;
			tree = tree.mLeft;
			wentLeftBits.set(pathFromRoot.size() - 1, true);
			while (tree.mRight != EMPTY) {
				pathFromRoot.add(tree);
				tree = tree.mRight;
				wentLeftBits.set(pathFromRoot.size() - 1, false);
			}
			assert tree.mLeft == EMPTY;
			newNode = empty();
			pathFromRoot.set(removeHeight, new FunctionalMap<>(removeTree.mLeft, removeTree.mRight, tree.mKey, tree.mValue, removeTree.mSizeColor));
			decreaseHeight = true;
		}
		while (!pathFromRoot.isEmpty()) {
			FunctionalMap<K, V> parent = pathFromRoot.remove(pathFromRoot.size() - 1);
			final boolean wentLeft = wentLeftBits.get(pathFromRoot.size());
			if (!decreaseHeight) {
				// only update size and child pointer
				newNode = new FunctionalMap<>(wentLeft ? newNode : parent.mLeft, wentLeft ? parent.mRight : newNode,
						parent.mKey, parent.mValue,
						parent.mSizeColor < 0 ? parent.mSizeColor + 1 : parent.mSizeColor - 1);
			} else {
				FunctionalMap<K, V> realParent = parent;

				// check if parent is full
				boolean parentFull = !parent.isTwoNode();
				if (!parentFull && !pathFromRoot.isEmpty()) {
					final FunctionalMap<K, V> grandParent = pathFromRoot.get(pathFromRoot.size() - 1);
					if (!grandParent.isTwoNode() && grandParent.mRight == parent) {
						parentFull = true;
						realParent = pathFromRoot.remove(pathFromRoot.size() - 1);
					}
				}
				if (parentFull) {
					// we now have three keys in realParent and can just remove the node, replacing it by its children.
					decreaseHeight = false;
					if (parent == realParent) {
						if (wentLeft) {
							final FunctionalMap<K, V> sibling = parent.mRight;
							// make parent.mRight the new 2-node parent, with (newNode +
							// parent.mRight.mLeft) as left child.
							//   i1    i2
							// a' b1b2   c1c2
							//   blbmbr clcmcr
							//
							// -->   b1     i2
							//   i1      b2     c
							// a' bl   bm br  clcmcr
							if (sibling.mLeft.isTwoNode()) {
								final FunctionalMap<K, V> newLeft = new FunctionalMap<>(newNode, sibling.mLeft, parent.mKey,
										parent.mValue, false);
								newNode = new FunctionalMap<>(newLeft, sibling.mRight, sibling.mKey, sibling.mValue, true);
							} else {
								final FunctionalMap<K, V> newLeft = new FunctionalMap<>(newNode, sibling.mLeft.mLeft, parent.mKey,
										parent.mValue, true);
								final FunctionalMap<K, V> newRight= new FunctionalMap<>(sibling.mLeft.mRight, sibling.mRight, sibling.mKey,
										sibling.mValue, true);
								newNode = new FunctionalMap<>(newLeft, newRight, sibling.mLeft.mKey,
										sibling.mLeft.mValue, false);
							}
						} else {
							// we are actually the sibling. Just make us a child.
							newNode = new FunctionalMap<>(parent.mLeft, newNode, parent.mKey, parent.mValue, true);
						}
					} else if (wentLeft) {
						// removal was in the middle node
						// p1 p2
						// a1a2 b' c1c2
						// alamar clcmcr
						// --> p1
						// a1 a2 p2 c1
						// al am ar b' cl cr
						if (parent.mRight.isTwoNode()) {
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(newNode, parent.mRight,
									parent.mKey, parent.mValue, false);
							newNode = new FunctionalMap<>(realParent.mLeft, newRight, realParent.mKey,
									realParent.mValue, true);
						} else {
							final FunctionalMap<K, V> newRightLeft = new FunctionalMap<>(newNode, parent.mRight.mLeft,
									parent.mKey, parent.mValue, true);
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(newRightLeft, parent.mRight.mRight,
									parent.mRight.mKey, parent.mRight.mValue, true);
							newNode = new FunctionalMap<>(realParent.mLeft, newRight, realParent.mKey,
									realParent.mValue, false);
						}
					} else {
						// parent is the middle one, rotate left. Then replace right child.
						// i1 i2
						// a b c'
						//
						// --> i1
						// a ib i2
						// bl br c'
						if (parent.mLeft.isTwoNode()) {
							final FunctionalMap<K, V> newRightRight = new FunctionalMap<>(parent.mLeft.mRight, newNode,
									parent.mKey, parent.mValue, true);
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(parent.mLeft.mLeft, newRightRight,
									parent.mLeft.mKey, parent.mLeft.mValue, false);
							newNode = new FunctionalMap<>(realParent.mLeft, newRight, realParent.mKey, realParent.mValue,
									true);
						} else {
							// i1 i2
							// a b c'
							//
							// -> i1    b2
							// a     b1   i2
							//     bl bm br c'
							final FunctionalMap<K, V> newRightRight = new FunctionalMap<>(parent.mLeft.mRight.mRight, newNode,
									parent.mKey, parent.mValue, true);
							final FunctionalMap<K, V> newRightLeft = new FunctionalMap<>(parent.mLeft.mLeft, parent.mLeft.mRight.mLeft,
									parent.mLeft.mKey, parent.mLeft.mValue, true);
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(newRightLeft, newRightRight,
									parent.mLeft.mRight.mKey, parent.mLeft.mRight.mValue, true);
							newNode = new FunctionalMap<>(realParent.mLeft, newRight, realParent.mKey, realParent.mValue,
									false);

						}
					}
					parent = realParent;
				} else {
					// parent is a two-node. split the other node and decrease height.
					decreaseHeight = true;
					if (wentLeft) {
						if (parent.mRight.isTwoNode()) {
							// i1
							// a' b
							// -->
							// i1 b
							// a'
							newNode = new FunctionalMap<>(newNode, parent.mRight, parent.mKey, parent.mValue, false);
						} else {
							// i1
							// a' b1 b2
							// bl bm br
							// -->
							// b1
							// i1 b2
							// a' bl bm br
							final FunctionalMap<K, V> newLeft = new FunctionalMap<>(newNode, parent.mRight.mLeft,
									parent.mKey, parent.mValue, true);
							newNode = new FunctionalMap<>(newLeft, parent.mRight.mRight, parent.mRight.mKey,
									parent.mRight.mValue, true);
							decreaseHeight = false;
						}
					} else {
						// Make the left node a three-node and move its right child over.
						// i1
						// a1 a2 b'
						// al am ar
						// -->
						// a2
						// a1 i1
						// al am ar b'
						if (parent.mLeft.isTwoNode()) {
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(parent.mLeft.mRight, newNode,
									parent.mKey, parent.mValue, true);
							newNode = new FunctionalMap<>(parent.mLeft.mLeft, newRight, parent.mLeft.mKey,
									parent.mLeft.mValue, false);
						} else {
							final FunctionalMap<K, V> newLeft = new FunctionalMap<>(parent.mLeft.mLeft,
									parent.mLeft.mRight.mLeft, parent.mLeft.mKey, parent.mLeft.mValue, true);
							final FunctionalMap<K, V> newRight = new FunctionalMap<>(parent.mLeft.mRight.mRight,
									newNode, parent.mKey, parent.mValue, true);

							newNode = new FunctionalMap<>(newLeft, newRight, parent.mLeft.mRight.mKey,
									parent.mLeft.mRight.mValue, true);
							decreaseHeight = false;
						}
					}
				}
			}
		}
		return newNode;
	}

	public int getHeight() {
		int height = 0;
		FunctionalMap<K, V> tree = this;
		while (tree != EMPTY) {
			height++;
			tree = tree.mLeft;
		}
		return height;
	}

	@Override
	public K getKey() {
		return mKey;
	}

	@Override
	public V getValue() {
		return mValue;
	}

	@Override
	public V setValue(final V newValue) {
		throw new UnsupportedOperationException("Functional Maps are read-only");
	}

	@Override
	public Set<Entry<K, V>> entrySet() {
		return new EntrySet();
	}

	@Override
	public int size() {
		return Math.abs(mSizeColor);
	}

	private boolean isTwoNode() {
		return mSizeColor >= 0;
	}

	class EntrySet extends AbstractSet<Entry<K, V>> {
		@Override
		public Iterator<Entry<K, V>> iterator() {
			return new EntryIterator<>(FunctionalMap.this);
		}

		@Override
		public int size() {
			return FunctionalMap.this.size();
		}
	}

	static class EntryIterator<K, V> implements Iterator<Entry<K, V>> {
		ArrayDeque<FunctionalMap<K,V>> mPathFromRoot;

		EntryIterator(FunctionalMap<K, V> tree) {
			mPathFromRoot = new ArrayDeque<>();
			while (tree != EMPTY) {
				mPathFromRoot.add(tree);
				tree = tree.mLeft;
			}
		}

		@Override
		public boolean hasNext() {
			return !mPathFromRoot.isEmpty();
		}

		@Override
		public Entry<K,V> next() {
			final FunctionalMap<K,V> next = mPathFromRoot.removeLast();
			FunctionalMap<K, V> tree = next.mRight;
			while (tree != EMPTY) {
				mPathFromRoot.add(tree);
				tree = tree.mLeft;
			}
			return next;
		}
	}
}
