/**
 * Describes a handler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieTranslator;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public interface IHandler {
	/**
	 * The logger instance for all handler.
	 */
	static Logger s_Logger = CACSL2BoogieTranslator.s_Logger;
	
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
