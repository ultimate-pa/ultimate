/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models;

/**
 *
 * @author dietsch
 *
 * @param <T>
 * @param <L>
 */
public class ModifiableLabeledEdgesMultigraph<T extends ModifiableLabeledEdgesMultigraph<T, L>, L>
		extends BaseLabeledEdgesMultigraph<T, L> {

	private static final long serialVersionUID = -3595056576172626796L;

	/**
	 * Adds an outgoing node to the corresponding list and updates the hashmap with the edge label accordingly.
	 *
	 * @param node
	 * @param label
	 * @return true iff the list update was succesful, only then the hashmap is updated, too.
	 */
	public boolean addOutgoingNode(final T node, final L label) {
		if (mOutgoingNodes.add(node)) {
			mOutgoingEdgeLabels.add(label);
			return true;
		}
		return false;
	}

	/**
	 * Removes an outgoing node from the corresponding list and updates the hashmap with the edge label accordingly.
	 *
	 * @param node
	 * @param label
	 * @return true iff the list update was successful, only then the hashmap is updated, too.
	 */
	public boolean removeOutgoingNode(final T node) {
		final int index = mOutgoingNodes.indexOf(node);
		if (mOutgoingNodes.remove(index) != null) {
			mOutgoingEdgeLabels.remove(index);
			return true;
		}
		return false;
	}

	/**
	 * Adds an incoming node to the corresponding list.
	 *
	 * @param node
	 * @param label
	 * @return true iff the list update was successful.
	 */
	public boolean addIncomingNode(final T node) {
		return mIncomingNodes.add(node);
	}

	/**
	 * Remove an incoming node from the corresponding list.
	 *
	 * @param node
	 * @param label
	 * @return true iff the list update was succesful.
	 */
	public boolean removeIncomingNode(final T node) {
		return mIncomingNodes.remove(node);
	}

	/**
	 * Create an (non-explicit) outgoing edge to the given node with the given label. Updates the corresponding lists in
	 * the two nodes and updates the hashmap in "this".
	 *
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In the latter case, changes already made
	 *         are undone.
	 */
	@SuppressWarnings("unchecked")
	public boolean connectOutgoing(final T node, final L label) {
		assert label != null;
		if (mOutgoingNodes.add(node)) {
			if (node.mIncomingNodes.add((T) this)) {
				mOutgoingEdgeLabels.add(label);
				return true;
			}
			mOutgoingNodes.remove(node);
			return false;
		}
		return false;
	}

	/**
	 * Removes an (non-explicit) outgoing edge from the given node. Updates the corresponding lists in the two nodes and
	 * updates the hashmap in the node "this".
	 *
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In the latter case, changes already made
	 *         are undone.
	 */
	public boolean disconnectOutgoing(final T node) {
		final int index = mOutgoingNodes.indexOf(node);
		if (mOutgoingNodes.remove(index) != null) {
			if (node.mIncomingNodes.remove(this)) {
				mOutgoingEdgeLabels.remove(index);
				return true;
			}
			mOutgoingNodes.add(node);
			return false;
		}
		return false;
	}

	/**
	 * Creates an (non-explicit) incoming edge from the given node with the given label. Updates the corresponding lists
	 * in the two nodes and updates the hashmap in the node given as the first argument.
	 *
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In the latter case, changes already made
	 *         are undone.
	 */
	@SuppressWarnings("unchecked")
	public boolean connectIncoming(final T node, final L label) {
		assert label != null;
		if (mIncomingNodes.add(node)) {
			if (node.mOutgoingNodes.add((T) this)) {
				node.mOutgoingEdgeLabels.add(label);
				return true;
			}
			mIncomingNodes.remove(node);
			return false;
		}
		return false;
	}

	/**
	 * Removes an (non-explicit) incoming edge from the given node. Updates the corresponding lists in the two nodes and
	 * updates the hashmap in the node given as an argument.
	 *
	 * @param node
	 * @param label
	 * @return true iff the adding operations were successful, false otherwise. In the latter case, changes already made
	 *         are undone.
	 */
	public boolean disconnectIncoming(final T node) {
		if (mIncomingNodes.remove(node)) {
			final int index = node.mOutgoingNodes.indexOf(this);
			if (node.mOutgoingNodes.remove(index) != null) {
				node.mOutgoingEdgeLabels.remove(index);
				return true;
			}
			mIncomingNodes.add(node);
			return false;
		}
		return false;
	}
}
