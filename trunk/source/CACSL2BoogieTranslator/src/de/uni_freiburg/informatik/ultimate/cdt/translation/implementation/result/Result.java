/**
 * Describing a translation result.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class Result {
	/**
	 * AST node.
	 */
    public ASTNode node;
    
	/**
	 * Constructor.
	 * 
	 * @param node
	 *            the node to hold in the line.
	 */
    public Result(ASTNode node) {
    	this.node = node;
    }
}
