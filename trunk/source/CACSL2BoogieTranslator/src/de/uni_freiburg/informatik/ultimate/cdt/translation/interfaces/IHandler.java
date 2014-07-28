/**
 * Describes a handler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public interface IHandler {
	
	/**
	 * Visit a given C node.
	 * 
	 * @param main
	 *            reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
    public Result visit(Dispatcher main, IASTNode node);
    
	/**
	 * Visit a given ACSL node.
	 * 
	 * @param main
	 *            reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
    public Result visit(Dispatcher main, ACSLNode node);
}
