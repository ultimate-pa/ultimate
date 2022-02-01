/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;

/**
 * A preprocessor directive, e.g. #include, #define, #pragma, #if etc. getASTNode() always returns a non-null
 * IASTPreprocessorStatement (which is admittedly not exactly useful by itself).
 */
public interface IPSTDirective extends IPSTPreprocessorNode {
	@Override
	IASTPreprocessorStatement getAstNode();
	
	/**
	 * @return {@code true} iff the PST directive is a conditional directive.
	 */
	default boolean isConditionalDirective() {
		final IASTPreprocessorStatement statement = getAstNode();
		return statement instanceof IASTPreprocessorIfStatement || statement instanceof IASTPreprocessorIfdefStatement
				|| statement instanceof IASTPreprocessorIfndefStatement
				|| statement instanceof IASTPreprocessorElseStatement
				|| statement instanceof IASTPreprocessorElifStatement
				|| statement instanceof IASTPreprocessorEndifStatement;
	}
}
