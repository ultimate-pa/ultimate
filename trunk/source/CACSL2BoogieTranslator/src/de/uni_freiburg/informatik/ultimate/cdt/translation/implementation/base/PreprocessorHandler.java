/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
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
        ILocation loc = LocationFactory.createCLocation(node);
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
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorElseStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorEndifStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorErrorStatement node) {
        String msg = "PreprocessorHandler: There was an error while parsing the preprocessor statements!";
        ILocation loc = LocationFactory.createCLocation(node);
        throw new IncorrectSyntaxException(loc, msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfdefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfndefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIfStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorIncludeStatement node) {
//        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
//        ILocation loc = new CACSLLocation(node);
//        Dispatcher.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorMacroDefinition node) {
        // this was already handled by the CDT  parser...
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorPragmaStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }

    @Override
    public Result visit(Dispatcher main, IASTPreprocessorUndefStatement node) {
        String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
        ILocation loc = LocationFactory.createCLocation(node);
        main.unsupportedSyntax(loc, msg);
        return new SkipResult();
    }
}
