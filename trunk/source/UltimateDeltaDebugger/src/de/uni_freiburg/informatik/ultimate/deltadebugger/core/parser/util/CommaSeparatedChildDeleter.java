/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Helper class to delete a subset of comma separated nodes including the neccesary amount of commas. Override
 * deleteComma and deleteNode to actually perform the required deletion.
 *
 */
public abstract class CommaSeparatedChildDeleter {

	private final List<IPSTNode> mChildrenToDelete;
	private final List<CommaSeparatedChild> mAllChildren;
	private ISourceRange mLeftComma;

	/**
	 * Constructor.
	 *
	 * @param childrenToDelete
	 *            sorted sub-sequence of the nodes in allChildren
	 * @param allChildren
	 *            sorted list of all children (see {@link CommaSeparatedChildFinder})
	 * @throws MissingChildException
	 *             if more nodes are supposed to be deleted than children exist
	 */
	public CommaSeparatedChildDeleter(final List<IPSTNode> childrenToDelete,
			final List<CommaSeparatedChild> allChildren) {
		mChildrenToDelete = childrenToDelete;
		mAllChildren = allChildren;

		if (childrenToDelete.size() > allChildren.size()) {
			throw new MissingChildException("cannot delete more nodes than children exist");
		}
	}

	private void deleteChildBeforeLast(final IPSTNode child, final ISourceRange rightComma)
			throws MissingCommaLocationException {
		// Delete comma to the left if there still is one, so we don't get a
		// problem if we delete all remaining elements
		if (mLeftComma != null) {
			deleteComma(mLeftComma);
			deleteNode(child);
			mLeftComma = rightComma;
		} else if (rightComma != null) {
			deleteNode(child);
			deleteComma(rightComma);
			mLeftComma = null;
		} else {
			throw new MissingCommaLocationException("Unable to delete child before last: " + child);
		}
	}

	/**
	 * Delete the nodes and necessary commas.
	 * 
	 * @throws MissingCommaLocationException if a required comma location is unknown
	 * @throws MissingChildException if child is missing
	 */
	public void deleteChildren() throws MissingCommaLocationException {
		final Iterator<IPSTNode> iter = mChildrenToDelete.iterator();
		if (!iter.hasNext()) {
			return;
		}

		IPSTNode childToDelete = iter.next();
		for (int i = 0; i < mAllChildren.size() - 1; ++i) {
			// Skip children that are not to be deleted and remember comma to the left
			final CommaSeparatedChild pos = mAllChildren.get(i);
			if (!childToDelete.equals(pos.node())) {
				mLeftComma = pos.nextCommaLocation();
				continue;
			}

			deleteChildBeforeLast(childToDelete, pos.nextCommaLocation());
			if (!iter.hasNext()) {
				return;
			}
			childToDelete = iter.next();
		}

		final CommaSeparatedChild lastPos = mAllChildren.get(mAllChildren.size() - 1);
		if (!childToDelete.equals(lastPos.node()) || iter.hasNext()) {
			// This may happen if the list is not sorted or if the list contains
			// unrelated (non-regular) nodes -> logic error
			throw new MissingChildException("Invalid child to delete in list: " + childToDelete);
		}
		deleteLastChild(childToDelete, lastPos.nextCommaLocation());
	}

	protected abstract void deleteComma(ISourceRange location);

	private void deleteLastChild(final IPSTNode child, final ISourceRange rightComma)
			throws MissingCommaLocationException {
		// Delete the comma to the left if at least one child will be left
		if (mChildrenToDelete.size() <= mAllChildren.size() - 1) {
			if (mLeftComma == null) {
				throw new MissingCommaLocationException("Unable to delete last child: " + child);
			}
			deleteComma(mLeftComma);
			mLeftComma = null;
		}

		deleteNode(child);

		// Remove an optionally existing trailing comma as well
		if (rightComma != null) {
			deleteComma(rightComma);
		}
	}

	protected abstract void deleteNode(IPSTNode node);

	/**
	 * Thrown if the deletion of a node is requested, which is not part of the comma separated children list. This is a
	 * logic error in the calling code.
	 */
	public static class MissingChildException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public MissingChildException(final String message) {
			super(message);
		}
	}

	/**
	 * Thrown if the deletion of a node requires the deletion of a comma, of which no location is known.
	 */
	public static class MissingCommaLocationException extends Exception {
		private static final long serialVersionUID = 1L;

		public MissingCommaLocationException(final String message) {
			super(message);
		}
	}
}
