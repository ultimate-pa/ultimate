/**
 * Breadth first search iterator.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
class DecoratorIteratorBreadthFirstSearch implements Iterator<DecoratorNode> {
	/**
	 * Buffer queue.
	 */
	Queue<DecoratorNode> queue = new LinkedList<DecoratorNode>();

	/**
	 * Constructor.
	 * 
	 * @param root
	 *            The root node to start from.
	 */
	public DecoratorIteratorBreadthFirstSearch(DecoratorNode root) {
		if (root != null) {
			queue.add(root);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see java.util.Iterator#remove()
	 */
	@Override
	public void remove() {
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * @see java.util.Iterator#hasNext()
	 */
	@Override
	public boolean hasNext() {
		return !queue.isEmpty();
	}

	/*
	 * (non-Javadoc)
	 * @see java.util.Iterator#next()
	 */
	@Override
	public DecoratorNode next() {
		if (!hasNext()) {
			throw new NoSuchElementException();
		}
		queue.addAll(queue.peek().getChildren());
		return queue.poll();
	}
}