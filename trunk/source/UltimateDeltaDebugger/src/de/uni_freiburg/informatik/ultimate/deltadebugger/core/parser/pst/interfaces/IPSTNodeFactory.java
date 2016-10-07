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

public interface IPSTNodeFactory {

	IPSTComment createComment(ISourceRange location, IASTComment comment);

	/*
	 * IPSTNodeBlock
	 */
	IPSTConditionalBlock createConditionalBlock(ISourceRange location, List<IPSTDirective> conditionalDirectives,
			ISourceRange activeBranchLocation);

	IPSTDirective createDirective(ISourceRange location, IASTPreprocessorStatement statement);

	IPSTIncludeDirective createIncludeDirective(ISourceRange location, IASTPreprocessorIncludeStatement include);

	/*
	 * IPSTPreprocessorNode
	 */
	IPSTMacroExpansion createMacroExpansion(ISourceRange location, IASTPreprocessorMacroExpansion expansion);

	IPSTOverlappingRegion createOverlappingRegion(ISourceRange location);

	/*
	 * IPSTRegularNode
	 */
	IPSTRegularNode createRegularNode(ISourceRange location, IASTNode astNode);

	IPSTTranslationUnit createTranslationUnit(ISourceRange location, IASTTranslationUnit tu);

	void setSourceDocument(ISourceDocument sourceDocument);

}
