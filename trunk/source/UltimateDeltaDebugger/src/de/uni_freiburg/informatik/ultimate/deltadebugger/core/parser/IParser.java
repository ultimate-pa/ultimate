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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.model.ILanguage;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Simplified Parser interface to remove configuration and boilerplate from variant generators. Ensures a consistent
 * parser configuration and default settings.
 */
public interface IParser {
	/**
	 * @param ast
	 *            AST.
	 * @param sourceDocument
	 *            source document
	 * @return PST
	 */
	IPSTTranslationUnit createPst(IASTTranslationUnit ast, ISourceDocument sourceDocument);
	
	/**
	 * Parse a source code from string and create a new AST instance.
	 * Default options are {@link ILanguage#OPTION_IS_SOURCE_UNIT} and {@link ILanguage#OPTION_NO_IMAGE_LOCATIONS} The
	 * most interesting additional option should be {@link ILanguage#OPTION_SKIP_FUNCTION_BODIES} to speed up the
	 * parsing.
	 *
	 * @param source
	 *            source code string
	 * @return new AST instance
	 */
	IASTTranslationUnit parse(String source);
	
	/**
	 * Parse a source code from string and create a new AST instance.
	 *
	 * @param source
	 *            source code string
	 * @param options
	 *            options
	 * @return new AST instance
	 * @see org.eclipse.cdt.core.model.ILanguage for possible options
	 */
	IASTTranslationUnit parse(String source, int options);
}
