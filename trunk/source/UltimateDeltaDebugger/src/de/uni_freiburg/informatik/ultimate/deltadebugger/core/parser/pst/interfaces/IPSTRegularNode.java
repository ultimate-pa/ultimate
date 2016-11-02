package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTNode;

/**
 * A regular node is an IASTNode from the original AST, i.e. it is not a preprocessor node. getASTNode() is never null.
 */
public interface IPSTRegularNode extends IPSTNode {

	/**
	 * @param astNode
	 *            immediate child node to find
	 * @return corrsponding regular node or null if not found
	 */
	IPSTRegularNode findRegularChild(IASTNode astNode);
}
