package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;


/**
 * Helper class to delete a subset of comma separated nodes including the
 * neccesary amount of commas. Override deleteComma and deleteNode to actually
 * perform the required deletion.
 *
 */
public abstract class CommaSeparatedChildDeleter {
	private final List<IPSTNode> childrenToDelete;
	private final List<CommaSeparatedChild> allChildren;
	private ISourceRange leftComma = null;

	
	/**
	 * Thrown if the deletion of a node requires the deletion of a comma, of
	 * which no location is known.
	 */
	public static class MissingCommaLocationException extends Exception {
		public MissingCommaLocationException(String message) {
			super(message);
		}
	}
	
	/**
	 * Thrown if the deletion of a node is requested, which is not part of the
	 * comma separated children list. This is a logic error in the
	 * calling code.
	 */
	public static class MissingChildException extends RuntimeException {
		public MissingChildException(String message) {
			super(message);
		}
	}
	
	/**
	 * @param childrenToDelete sorted sub-sequence of the nodes in allChildren
	 * @param allChildren sorted list of all children (see {@link CommaSeparatedChildFinder})
	 * @throws MissingChildException
	 */
	public CommaSeparatedChildDeleter(List<IPSTNode> childrenToDelete, List<CommaSeparatedChild> allChildren) {
		this.childrenToDelete = childrenToDelete;
		this.allChildren = allChildren;

		if (childrenToDelete.size() > allChildren.size()) {
			throw new MissingChildException("cannot delete more nodes than children exist");
		}
	}

	protected abstract void deleteComma(ISourceRange location);
	protected abstract void deleteNode(IPSTNode node);

	
	/**
	 * Delete the nodes and necessary commas
	 * @throws MissingCommaLocationException 
	 * @throws MissingChildException
	 */
	public void deleteChildren() throws MissingCommaLocationException {
		final Iterator<IPSTNode> iter = childrenToDelete.iterator();
		if (!iter.hasNext()) {
			return;
		}
		
		IPSTNode childToDelete = iter.next();
		for (int i = 0; i < allChildren.size() - 1; ++i) {
			// Skip children that are not to be deleted and remember comma to the left
			CommaSeparatedChild pos = allChildren.get(i);
			if (pos.node() != childToDelete) {
				leftComma = pos.nextCommaLocation();
				continue;
			}
			
			deleteChildBeforeLast(childToDelete, pos.nextCommaLocation());
			if (!iter.hasNext()) {
				return;
			}
			childToDelete = iter.next();
		}

		final CommaSeparatedChild lastPos = allChildren.get(allChildren.size()-1);
		if (childToDelete != lastPos.node() || iter.hasNext()) {
			// This may happen if the list is not sorted or if the list contains 
			// unrelated (non-regular) nodes -> logic error
			throw new MissingChildException("Invalid child to delete in list: " + childToDelete);
		}
		deleteLastChild(childToDelete, lastPos.nextCommaLocation());
	}

	private void deleteChildBeforeLast(IPSTNode child, ISourceRange rightComma)
			throws MissingCommaLocationException {
		// Delete comma to the left if there still is one, so we don't get a 
		// problem if we delete all remaining elements
		if (leftComma != null) {
			deleteComma(leftComma);
			deleteNode(child);
			leftComma = rightComma;
		} else if (rightComma != null) {
			deleteNode(child);
			deleteComma(rightComma);
			leftComma = null;
		} else {
			throw new MissingCommaLocationException("Unable to delete child before last: " + child);
		}
	}

	private void deleteLastChild(IPSTNode child, ISourceRange rightComma)
			throws MissingCommaLocationException {
		// Delete the comma to the left if more than one child will be left
		if (childrenToDelete.size() < allChildren.size() - 1) {
			if (leftComma == null) {
				throw new MissingCommaLocationException("Unable to delete last child: " + child);
			}
			deleteComma(leftComma);
			leftComma = null;
		}

		deleteNode(child);

		// Remove an optionally existing trailing comma as well
		if (rightComma != null) {
			deleteComma(rightComma);
		}
	}
	
}