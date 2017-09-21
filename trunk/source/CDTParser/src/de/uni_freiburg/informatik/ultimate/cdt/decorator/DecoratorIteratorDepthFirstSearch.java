/*
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
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
	Stack<DecoratorNode> mStack = new Stack<>();

	/**
	 * Constructor.
	 *
	 * @param root
	 *            The root node to start from.
	 */
	public DecoratorIteratorDepthFirstSearch(final DecoratorNode root) {
		if (root != null) {
			mStack.add(root);
		}
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean hasNext() {
		return !mStack.isEmpty();
	}

	@Override
	public DecoratorNode next() {
		if (!hasNext()) {
			throw new NoSuchElementException();
		}
		final DecoratorNode result = mStack.pop();
		for (int i = result.getChildren().size() - 1; i >= 0; i--) {
			mStack.add(result.getChildren().get(i));
		}
		return result;
	}
}
