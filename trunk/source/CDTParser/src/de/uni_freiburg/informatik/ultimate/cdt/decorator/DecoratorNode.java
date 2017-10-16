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
 * A decorator node, mapping ACSL ASTs into the CDT AST.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.02.2012
 */
public class DecoratorNode implements Iterable<DecoratorNode> {
	/**
	 * The C node.
	 */
	protected IASTNode mCNode;
	/**
	 * The ACSL node.
	 */
	protected ACSLNode mAcslNode;
	/**
	 * DecoratorNode children.
	 */
	private final List<DecoratorNode> mChildren;
	/**
	 * DecoratorNode parent.
	 */
	private final DecoratorNode mParent;

	/**
	 * Constructor.
	 *
	 * @param parent
	 *            the parent node
	 * @param acslNode
	 *            the ACSL AST node
	 */
	public DecoratorNode(final DecoratorNode parent, final ACSLNode acslNode) {
		this(parent);
		this.mAcslNode = acslNode;
	}

	/**
	 * Constructor.
	 *
	 * @param parent
	 *            the parent node
	 * @param cNode
	 *            the CDT AST Node
	 */
	public DecoratorNode(final DecoratorNode parent, final IASTNode cNode) {
		this(parent);
		this.mCNode = cNode;
	}

	/**
	 * Constructor.
	 *
	 * @param parent
	 *            the reference to the parent node
	 */
	public DecoratorNode(final DecoratorNode parent) {
		mChildren = new ArrayList<>();
		this.mParent = parent;
	}

	/**
	 * Whether this node has children or not.
	 *
	 * @return true iff this node has children
	 */
	public boolean hasChildren() {
		return !mChildren.isEmpty();
	}

	/**
	 * Add a new children to the decorator.
	 *
	 * @param child
	 *            decorator node
	 */
	public void addChildren(final DecoratorNode child) {
		if (mAcslNode != null) {
			throw new IllegalArgumentException("DecoratorNode with ACSL can not have children!");
		} else if (mCNode != null) {
			mChildren.add(child);
		} else {
			throw new IllegalArgumentException("Node has neither ACSL nor C!");
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mCNode != null) {
			sb.append(mCNode);
		} else if (mAcslNode != null) {
			sb.append(mAcslNode);
		}
		return sb.toString();
	}

	/**
	 * Getter for the parent node.
	 *
	 * @return the parent in the decorator tree.
	 */
	public DecoratorNode getParent() {
		return mParent;
	}

	/**
	 * Getter for the acsl ast node.
	 *
	 * @return an acsl ast node or null
	 */
	public ACSLNode getAcslNode() {
		return mAcslNode;
	}

	/**
	 * Getter for the cdt ast node.
	 *
	 * @return the cdt ast node or null
	 */
	public IASTNode getCNode() {
		return mCNode;
	}

	/**
	 * Generates and return a depth first search iterator.
	 */
	@Override
	public Iterator<DecoratorNode> iterator() {
		return new DecoratorIteratorDepthFirstSearch(this);
	}

	/**
	 * Generates and return a breadth first search iterator.
	 *
	 * @return a breadth first search iterator.
	 */
	public Iterator<DecoratorNode> iteratorBreadthFirst() {
		return new DecoratorIteratorBreadthFirstSearch(this);
	}

	/**
	 * Getter for children.
	 *
	 * @return the childrens of this node
	 */
	public List<DecoratorNode> getChildren() {
		return mChildren;
	}

	/**
	 * Add all new children to the decorator.
	 *
	 * @param children
	 *            list of decorator nodes to add
	 */
	public void addAllChildren(final List<DecoratorNode> children) {
		if (mAcslNode != null) {
			throw new IllegalArgumentException("DecoratorNode with ACSL can not have children!");
		} else if (mCNode != null) {
			this.mChildren.addAll(children);
		} else {
			throw new IllegalArgumentException("Node has neither ACSL nor C!");
		}
	}
}
