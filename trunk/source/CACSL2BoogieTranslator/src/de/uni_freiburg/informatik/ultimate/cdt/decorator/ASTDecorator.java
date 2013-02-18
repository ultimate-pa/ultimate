/**
 * Parser example extended with a CDT-AST decorator to support ACSL-ASTs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public class ASTDecorator {
	/**
	 * All ACSL ASTs in the file, specified with there root node.
	 */
	private List<ACSLNode> acslASTs;
	/**
	 * The root node of the decorator.
	 */
	private DecoratorNode rootNode;
	/**
	 * Helper variable, required for mapASTs().
	 */
	private int currentStartLineNr;

	/**
	 * Entry point to recursive method to generate the mapping between CDT AST
	 * and ACSL ASTs. A translation unit without any C code will return null!
	 * Pure ACSL code is skipped therefore!
	 * 
	 * @param node
	 *            the start node
	 */
	public void mapASTs(IASTNode node) {
		if(!(node instanceof IASTTranslationUnit)) {
			throw new IllegalArgumentException("First node of C-AST must be TU!");
		}
		currentStartLineNr = 1;
		DecoratorNode result = mapASTs(node, null).get(0);
		assert acslASTs.isEmpty();
		setRootNode(result);
	}

	/**
	 * Recursive method to generate the mapping between CDT AST and ACSL ASTs.
	 * 
	 * @param node
	 *            the current node
	 * @param parent
	 *            the current parent (null for root node)
	 * @return the children list or null
	 */
	private List<DecoratorNode> mapASTs(IASTNode node, DecoratorNode parent) {
		if (node.getFileLocation() == null)
			return null;

		// there is acsl between the previous node and this one.
		List<DecoratorNode> list = new ArrayList<DecoratorNode>();
		if (parent != null && containsAcsl(currentStartLineNr, node.getFileLocation()
				.getStartingLineNumber())) {
			list.addAll(getAllTheAcsl(parent, currentStartLineNr, node
					.getFileLocation().getStartingLineNumber()));
		}

		if (!containsAcsl(node)) {
			currentStartLineNr = node.getFileLocation().getEndingLineNumber() + 1;
			list.add(new DecoratorNode(parent, node));
			return list;
		}
		// there is ACSL ... take care for all the children
		DecoratorNode result = new DecoratorNode(parent, node);
		list.add(result);
		for (int i = 0; i < node.getChildren().length; i++) {
			if (i == 0) {
				currentStartLineNr = node.getFileLocation()
						.getStartingLineNumber();
			}
			List<DecoratorNode> newChildren = mapASTs(node.getChildren()[i],
					result);
			for (int j = 0; j < newChildren.size(); j++) {
				if (newChildren.get(j) != null) {
					result.addChildren(newChildren.get(j));
				}
			}
		}
		if (containsAcsl(currentStartLineNr, node.getFileLocation()
				.getEndingLineNumber() + 1)) {
			// there is acsl between last children and node end ...
			result.addAllChildren(getAllTheAcsl(result, currentStartLineNr,
					node.getFileLocation().getEndingLineNumber()));
		}
		currentStartLineNr = node.getFileLocation().getEndingLineNumber();
		return list;
	}

	/**
	 * This method returns all ACSL comments between start and end.
	 * 
	 * @param parent
	 *            the parent decorator node
	 * @param start
	 *            the start line number (inclusive)
	 * @param end
	 *            the end line number (inclusive)
	 * @return the acsl ast node
	 */
	private List<DecoratorNode> getAllTheAcsl(DecoratorNode parent, int start,
			int end) {
		List<DecoratorNode> list = new ArrayList<DecoratorNode>();
		for (int i = 0; i < acslASTs.size(); i++) {
			if (acslASTs.get(i).getEndingLineNumber() <= end
					&& acslASTs.get(i).getStartingLineNumber() >= start) {
				list.add(new DecoratorNode(parent, acslASTs.remove(i--)));
			}
		}
		return list;
	}

	/**
	 * Determines whether the given node contains ACSL statements or not.
	 * 
	 * @param node
	 *            the node to check
	 * @return true iff the given node contains ACSL statements.
	 */
	private boolean containsAcsl(IASTNode node) {
		if (node.getFileLocation() == null)
			return false;
		int start = node.getFileLocation().getStartingLineNumber();
		int end = node.getFileLocation().getEndingLineNumber();
		return containsAcsl(start, end);
	}

	/**
	 * Determines whether the given line numbers contain ACSL statements.
	 * 
	 * @param start
	 *            the start of the block (incl)
	 * @param end
	 *            the end of the block (incl)
	 * @return true iff the given line numbers contain ACSL statements.
	 */
	private boolean containsAcsl(int start, int end) {
		for (ACSLNode acsl : this.acslASTs) {
			if (start <= acsl.getStartingLineNumber()
					&& end >= acsl.getEndingLineNumber()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Getter for root node.
	 * 
	 * @return the rootNode
	 */
	public DecoratorNode getRootNode() {
		return rootNode;
	}

	/**
	 * Setter for root node.
	 * 
	 * @param node
	 *            the root node
	 */
	private void setRootNode(DecoratorNode node) {
		this.rootNode = node;
	}

	/**
	 * Setter for the ACSL AST list.
	 * 
	 * @param acslASTs
	 *            the acslASTs to set
	 */
	public void setAcslASTs(List<ACSLNode> acslASTs) {
		this.acslASTs = acslASTs;
	}
}
