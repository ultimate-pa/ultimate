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
	protected IASTNode cNode;
	/**
	 * The ACSL node.
	 */
	protected ACSLNode acslNode;
	/**
	 * DecoratorNode children.
	 */
	private List<DecoratorNode> children;
	/**
	 * DecoratorNode parent.
	 */
	private DecoratorNode parent;

	/**
	 * Constructor.
	 * 
	 * @param parent
	 *            the parent node
	 * @param acslNode
	 *            the ACSL AST node
	 */
	public DecoratorNode(DecoratorNode parent, ACSLNode acslNode) {
		this(parent);
		this.acslNode = acslNode;
	}

	/**
	 * Whether this node has children or not.
	 * 
	 * @return true iff this node has children
	 */
	public boolean hasChildren() {
		return !children.isEmpty();
	}

	/**
	 * Constructor.
	 * 
	 * @param parent
	 *            the parent node
	 * @param cNode
	 *            the CDT AST Node
	 */
	public DecoratorNode(DecoratorNode parent, IASTNode cNode) {
		this(parent);
		this.cNode = cNode;
	}

	/**
	 * Constructor.
	 * 
	 * @param parent
	 *            the reference to the parent node
	 */
	public DecoratorNode(DecoratorNode parent) {
		this.children = new ArrayList<DecoratorNode>();
		this.parent = parent;
	}

	/**
	 * Add a new children to the decorator.
	 * 
	 * @param child
	 *            decorator node
	 */
	public void addChildren(DecoratorNode child) {
		if (this.acslNode != null)
			throw new IllegalArgumentException(
					"DecoratorNode with ACSL can not have children!");
		else if (this.cNode != null) {
			this.children.add(child);
		} else {
			throw new IllegalArgumentException("Node has neither ACSL nor C!");
		}
	}

	/**
	 * Add all new children to the decorator.
	 * 
	 * @param children
	 *            list of decorator nodes to add
	 */
	public void addAllChildren(List<DecoratorNode> children) {
		if (this.acslNode != null)
			throw new IllegalArgumentException(
					"DecoratorNode with ACSL can not have children!");
		else if (this.cNode != null) {
			this.children.addAll(children);
		} else {
			throw new IllegalArgumentException("Node has neither ACSL nor C!");
		}
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (cNode != null) {
			sb.append(cNode);
		} else if (acslNode != null) {
			sb.append(acslNode);
		}
		return sb.toString();
	}

	/**
	 * Getter for the parent node.
	 * 
	 * @return the parent in the decorator tree.
	 */
	public DecoratorNode getParent() {
		return parent;
	}

	/**
	 * Getter for the acsl ast node.
	 * 
	 * @return an acsl ast node or null
	 */
	public ACSLNode getAcslNode() {
		return acslNode;
	}

	/**
	 * Getter for the cdt ast node.
	 * 
	 * @return the cdt ast node or null
	 */
	public IASTNode getCNode() {
		return cNode;
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
		return children;
	}
}
