/**
 * Depth first search iterator. Will return the nodes in the order as they occur
 * in the file.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Stack;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
class DecoratorIteratorDepthFirstSearch implements Iterator<DecoratorNode> {
	/**
	 * Buffer stack.
	 */
	Stack<DecoratorNode> stack = new Stack<DecoratorNode>();

	/**
	 * Constructor.
	 * 
	 * @param root
	 *            The root node to start from.
	 */
	public DecoratorIteratorDepthFirstSearch(DecoratorNode root) {
		if (root != null)
			stack.add(root);
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
		return !stack.isEmpty();
	}

	/*
	 * (non-Javadoc)
	 * @see java.util.Iterator#next()
	 */
	@Override
	public DecoratorNode next() {
		if (!hasNext())
			throw new NoSuchElementException();
		DecoratorNode result = stack.pop();
		for (int i = result.getChildren().size() - 1; i >= 0; i--) {
			stack.add(result.getChildren().get(i));
		}
		return result;
	}
}