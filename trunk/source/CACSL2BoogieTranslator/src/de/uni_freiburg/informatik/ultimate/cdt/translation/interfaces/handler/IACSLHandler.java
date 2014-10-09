/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 28.02.2012
 */
public interface IACSLHandler extends IHandler {
	/**
	 * Translates an CodeAnnot.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, CodeAnnot node);
	
	/**
	 * Translates an BinaryExpression.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, BinaryExpression node);
	
	/**
	 * Translates an UnaryExpression.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, UnaryExpression node);
	
	/**
	 * Translates an IntegerLiteral.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, IntegerLiteral node);
	
	/**
	 * Translates an BooleanLiteral.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, BooleanLiteral node);
	
	/**
	 * Translates an RealLiteral.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, RealLiteral node);
	
	/**
	 * Translates an IdentifierExpression.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, IdentifierExpression node);
	
	/**
	 * Translates an Contract.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, Contract node);
	
	/**
	 * Translates an Requires.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, Requires node);
	
	/**
	 * Translates an Ensures.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, Ensures node);
	
	/**
	 * Translates an Assigns.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, Assigns node);
	
	/**
	 * Translates an ResultExpression.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, ACSLResultExpression node);
	
	/**
	 * Translates an LoopAnnot.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, LoopAnnot node);
	
	/**
	 * Translates an LoopInvariant.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, LoopInvariant node);
	
	/**
	 * Translates an LoopVariant.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, LoopVariant node);
	
	/**
	 * Translates an LoopAssigns.
	 * 
	 * @param main
	 *            a reference to the main dispatcher
	 * @param node
	 *            the node to visit
	 * @return a result object
	 */
	public Result visit(Dispatcher main, LoopAssigns node);
	
	/**
     * Translates an ArrayAccessExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, ArrayAccessExpression node);
    
    /**
     * Translates an FieldAccessExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, FieldAccessExpression node);
    
    /**
     * Translates an FreeableExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, FreeableExpression node);
    
    /**
     * Translates an MallocableExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, MallocableExpression node);
    
    /**
     * Translates an ValidExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, ValidExpression node);
}
