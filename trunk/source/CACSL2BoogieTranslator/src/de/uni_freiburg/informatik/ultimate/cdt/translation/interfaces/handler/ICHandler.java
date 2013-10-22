/**
 * Describes a C+ACSL handler.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public interface ICHandler extends IHandler {
    /**
     * Holds the variables for the different scopes in a c program.
     * 
     * @return the variables in scopes.
     */
    public SymbolTable getSymbolTable();

    /**
     * Setter for the ACSL contract.
     * 
     * @param rc
     *            the contract to set, null to mark contract as handled.
     */
    public void clearContract();

    /**
     * Calculates and adds sizeof constants to the translation unit.
     * 
     * @param cvar
     *            the cvar to use, to calculate the constants.
     */
    public void addSizeOfConstants(CType cvar);

    /**
     * Checks resType, whether it needs some special treatment for pointers,
     * according the value in pointerOps.
     * Also in case the flag putOnHeap is set -- which is the case for our special
     * HeapVariables.
     * 
     * @param main
     *            a reference to the main Dispatcher.
     * @param pointerOps
     *            the pointer operator array.
     * @param resType
     *            the type to check.
     * @param putOnHeap
     *            indicates whether we are dealing with a HeapVar
     * @return the checked ResultTypes object.
     */
    public ResultTypes checkForPointer(Dispatcher main,
            IASTPointerOperator[] pointerOps, ResultTypes resType, boolean putOnHeap);

    /**
     * Translates an IASTTranslationUnit.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTTranslationUnit node);

    /**
     * Translates an IASTFunctionDefinition.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTFunctionDefinition node);

    /**
     * Translates an IASTCompundStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTCompoundStatement node);

    /**
     * Translates an IASTFunctionDeclarator.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTFunctionDeclarator node);

    /**
     * Translates an IASTSimpleDeclaration.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTSimpleDeclaration node);

    /**
     * Translates an IASTLiteralExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTLiteralExpression node);

    /**
     * Translates an IASTIdExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTIdExpression node);

    /**
     * Translates an IASTUnaryExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTUnaryExpression node);

    /**
     * Translates an IASTBinaryExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTBinaryExpression node);

    /**
     * Translates an IASTEqualsInitializer.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTEqualsInitializer node);

    /**
     * Translates an IASTDeclarationStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTDeclarationStatement node);

    /**
     * Translates an IASTReturnStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTReturnStatement node);

    /**
     * Translates an IASTExpressionStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTExpressionStatement node);

    /**
     * Translates an IASTIfStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTIfStatement node);

    /**
     * Translates an IASTWhileStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTWhileStatement node);

    /**
     * Translates an IASTForStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTForStatement node);

    /**
     * Translates an IASTDoStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTDoStatement node);

    /**
     * Translates an IASTExpressionList.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTExpressionList node);

    /**
     * Translates an IASTFunctionCallExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTFunctionCallExpression node);

    /**
     * Translates an IASTBreakStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTBreakStatement node);

    /**
     * Translates an CASTNullStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTNullStatement node);

    /**
     * Handles an IASTSwitchStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTSwitchStatement node);

    /**
     * Handles an IASTCaseStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTCaseStatement node);

    /**
     * Handles an IASTDefaultStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTDefaultStatement node);

    /**
     * Handles an IASTLabelStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTLabelStatement node);

    /**
     * Handles an IASTGotoStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTGotoStatement node);

    /**
     * Handles an IASTCastExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTCastExpression node);

    /**
     * Handles an IASTConditionalExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
	public Result visit(Dispatcher main, IASTConditionalExpression node);
    
    /**
     * Handles an IASTInitializerList.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTInitializerList node);

    /**
     * Handles an IASTArraySubscriptExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTArraySubscriptExpression node);

    /**
     * Handles an IASTInitializerClause.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTInitializerClause node);

    /**
     * Handles an IASTFieldReference (e.g. array field).
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTFieldReference node);

    /**
     * Handles an CASTDesignatedInitializer (e.g. struct initializer).
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, CASTDesignatedInitializer node);

    /**
     * Handles an IASTProblemStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTProblemStatement node);

    /**
     * Handles an IASTProblemDeclaration.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTProblemDeclaration node);

    /**
     * Handles an IASTProblemExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTProblemExpression node);

    /**
     * Handles an IASTProblem.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTProblem node);

    /**
     * Handles an IASTProblemTypeId.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTProblemTypeId node);

    /**
     * Handles an IASTPointer.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPointer node);

    /**
     * Handles an IASTTypeIdExpression.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTTypeIdExpression node);
}
