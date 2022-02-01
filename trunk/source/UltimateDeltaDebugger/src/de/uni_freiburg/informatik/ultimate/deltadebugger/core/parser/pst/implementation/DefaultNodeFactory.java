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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTOverlappingRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Default PST node factory.
 */
public class DefaultNodeFactory implements IPSTNodeFactory {
	protected ISourceDocument mSource;
	
	@Override
	public IPSTComment createComment(final ISourceRange location, final IASTComment comment) {
		return new PSTComment(mSource, location, comment);
	}
	
	@Override
	public IPSTConditionalBlock createConditionalBlock(final ISourceRange location,
			final List<IPSTDirective> conditionalDirectives, final ISourceRange activeBranchLocation) {
		return new PSTConditionalBlock(mSource, location, conditionalDirectives, activeBranchLocation);
	}
	
	@Override
	public IPSTDirective createDirective(final ISourceRange location, final IASTPreprocessorStatement statement) {
		return new PSTDirective(mSource, location, statement);
	}
	
	@Override
	public IPSTIncludeDirective createIncludeDirective(final ISourceRange location,
			final IASTPreprocessorIncludeStatement include) {
		return new PSTIncludeDirective(mSource, location, include);
	}
	
	@Override
	public IPSTMacroExpansion createMacroExpansion(final ISourceRange location,
			final IASTPreprocessorMacroExpansion expansion) {
		return new PSTMacroExpansion(mSource, location, expansion);
	}
	
	@Override
	public IPSTOverlappingRegion createOverlappingRegion(final ISourceRange location) {
		return new PSTOverlappingRegion(mSource, location);
	}
	
	@Override
	public IPSTRegularNode createRegularNode(final ISourceRange location, final IASTNode astNode) {
		return new PSTRegularNode(mSource, location, astNode);
	}
	
	@Override
	public IPSTTranslationUnit createTranslationUnit(final ISourceRange location,
			final IASTTranslationUnit translationUnit) {
		return new PSTTranslationUnit(mSource, location, translationUnit);
	}
	
	@Override
	public void setSourceDocument(final ISourceDocument sourceDocument) {
		mSource = sourceDocument;
	}
}
