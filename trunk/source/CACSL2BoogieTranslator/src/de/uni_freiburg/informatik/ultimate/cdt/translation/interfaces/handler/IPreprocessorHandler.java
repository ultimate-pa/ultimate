package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorErrorStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorPragmaStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorUndefStatement;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;

/**
 * @author Markus Lindenmann
 * @date 03.11.2012
 */
public interface IPreprocessorHandler extends IHandler {

    /**
     * Translates an IASTPreprocessorElifStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorElifStatement node);

    /**
     * Translates an IASTPreprocessorElseStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorElseStatement node);

    /**
     * Translates an IASTPreprocessorEndifStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorEndifStatement node);

    /**
     * Translates an IASTPreprocessorErrorStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorErrorStatement node);

    /**
     * Translates an IASTPreprocessorIfdefStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorIfdefStatement node);

    /**
     * Translates an IASTPreprocessorIfndefStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorIfndefStatement node);

    /**
     * Translates an IASTPreprocessorIfStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorIfStatement node);

    /**
     * Translates an IASTPreprocessorIncludeStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorIncludeStatement node);

    /**
     * Translates an IASTPreprocessorMacroDefinition.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorMacroDefinition node);

    /**
     * Translates an IASTPreprocessorPragmaStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorPragmaStatement node);

    /**
     * Translates an IASTPreprocessorUndefStatement.
     * 
     * @param main
     *            a reference to the main dispatcher
     * @param node
     *            the node to visit
     * @return a result object
     */
    public Result visit(Dispatcher main, IASTPreprocessorUndefStatement node);
}
