/**
 * Handler for Preprocessor Statements!
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import org.eclipse.cdt.core.dom.ast.IASTNode;
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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IPreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Markus Lindenmann
 * @date 03.11.2012
 */
public class PreprocessorHandler implements IPreprocessorHandler {

    @Override
    public Result visit(Dispatcher main, IASTNode node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        throw new UnsupportedSyntaxException(loc, msg);
    }

    /**
     * @deprecated is not supported in this handler! Do not use!
     */
    @Override
    public Result visit(Dispatcher main, ACSLNode node) {
        throw new UnsupportedOperationException(
                "Implementation Error: Use ACSLHandler for: " + node.getClass());
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorElifStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorElseStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorEndifStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorErrorStatement node) {
        String msg = "PreprocessorHandler: There was an error while parsing the preprocessor statements!";
        ILocation loc = new CACSLLocation(node);
        throw new IncorrectSyntaxException(loc, msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfdefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfndefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIncludeStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorMacroDefinition node) {
        // this was already handled by the CDT  parser...
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorPragmaStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorUndefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        Dispatcher.unsupportedSyntax(loc, msg);
        return new ResultSkip();
    }
}
