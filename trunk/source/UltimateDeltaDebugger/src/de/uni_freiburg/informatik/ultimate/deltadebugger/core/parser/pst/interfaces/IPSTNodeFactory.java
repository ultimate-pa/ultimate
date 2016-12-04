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

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * PST node factory interface.
 */
public interface IPSTNodeFactory {
	/**
	 * @param location
	 *            Source range.
	 * @param comment
	 *            AST comment
	 * @return PST comment
	 */
	IPSTComment createComment(ISourceRange location, IASTComment comment);
	
	/* IPSTNodeBlock */
	/**
	 * @param location
	 *            Source range.
	 * @param conditionalDirectives
	 *            list of condition directives
	 * @param activeBranchLocation
	 *            active branch location
	 * @return PST conditional block
	 */
	IPSTConditionalBlock createConditionalBlock(ISourceRange location, List<IPSTDirective> conditionalDirectives,
			ISourceRange activeBranchLocation);
	
	/**
	 * @param location
	 *            Source range.
	 * @param statement
	 *            AST preprocessor statement
	 * @return PST directive
	 */
	IPSTDirective createDirective(ISourceRange location, IASTPreprocessorStatement statement);
	
	/**
	 * @param location
	 *            Source range.
	 * @param include
	 *            AST include statement
	 * @return PST include directive
	 */
	IPSTIncludeDirective createIncludeDirective(ISourceRange location, IASTPreprocessorIncludeStatement include);
	
	/* IPSTPreprocessorNode */
	/**
	 * @param location
	 *            Source range.
	 * @param expansion
	 *            AST macro expansion
	 * @return PST macro expansion
	 */
	IPSTMacroExpansion createMacroExpansion(ISourceRange location, IASTPreprocessorMacroExpansion expansion);
	
	/**
	 * @param location
	 *            Source range.
	 * @return PST overlapping region
	 */
	IPSTOverlappingRegion createOverlappingRegion(ISourceRange location);
	
	/* IPSTRegularNode */
	/**
	 * @param location
	 *            Source range.
	 * @param astNode
	 *            AST node
	 * @return PST regular node
	 */
	IPSTRegularNode createRegularNode(ISourceRange location, IASTNode astNode);
	
	/**
	 * @param location
	 *            Source range.
	 * @param translationUnit
	 *            AST translation unit
	 * @return PST translation unit
	 */
	IPSTTranslationUnit createTranslationUnit(ISourceRange location, IASTTranslationUnit translationUnit);
	
	/**
	 * @param sourceDocument
	 *            Source document.
	 */
	void setSourceDocument(ISourceDocument sourceDocument);
}
