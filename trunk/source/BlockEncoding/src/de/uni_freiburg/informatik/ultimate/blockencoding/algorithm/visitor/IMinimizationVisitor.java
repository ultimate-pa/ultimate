/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;

/**
 * Basic interface for all Visitors on the new data model, these visitors can
 * Build, Minimize, Control or Print it.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IMinimizationVisitor {

	/**
	 * The basic traversal method, to do the recursive traversal of the
	 * underlying CFG. How the traversal is implement, depends mainly on the
	 * implementing Visitor-Class
	 * 
	 * @param node
	 *            the MinimizedNode to visit
	 */
	public void visitNode(MinimizedNode node);

}
