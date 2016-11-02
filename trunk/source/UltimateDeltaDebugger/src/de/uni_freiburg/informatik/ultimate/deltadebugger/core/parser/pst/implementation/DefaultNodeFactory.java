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

public class DefaultNodeFactory implements IPSTNodeFactory {

	private ISourceDocument mSource;

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
	public IPSTTranslationUnit createTranslationUnit(final ISourceRange location, final IASTTranslationUnit tu) {
		return new PSTTranslationUnit(mSource, location, tu);
	}

	@Override
	public void setSourceDocument(final ISourceDocument sourceDocument) {
		mSource = sourceDocument;
	}

}
