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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IPreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @date 03.11.2012
 */
public class PreprocessorHandler implements IPreprocessorHandler {

	private final boolean mIgnorePreprocessorPragmas;

	public PreprocessorHandler(final boolean ignorePreprocessorPragmas) {
		mIgnorePreprocessorPragmas = ignorePreprocessorPragmas;
	}

	@Override
	public Result visit(final Dispatcher main, final IASTNode node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorElifStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorElseStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorEndifStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorErrorStatement node) {
		final String msg = "PreprocessorHandler: There was an error while parsing the preprocessor statements!";
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorIfdefStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorIfndefStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorIfStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorIncludeStatement node) {
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorMacroDefinition node) {
		// this was already handled by the CDT parser...
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorPragmaStatement node) {
		if (mIgnorePreprocessorPragmas) {
			return new SkipResult();
		}
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}

	@Override
	public Result visit(final Dispatcher main, final IASTPreprocessorUndefStatement node) {
		final String msg = "PreprocessorHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createCLocation(node);
		main.unsupportedSyntax(loc, msg);
		return new SkipResult();
	}
}
