package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTMacroExpansion extends PSTNode implements IPSTMacroExpansion {

	public PSTMacroExpansion(final ISourceDocument source, final ISourceRange location,
			final IASTPreprocessorMacroExpansion expansion) {
		super(source, location, expansion);
	}

	@Override
	int dispatchLeave(final IPSTVisitor action) {
		return action.leave(this);
	}

	@Override
	int dispatchVisit(final IPSTVisitor action) {
		return action.visit(this);
	}

	@Override
	public IASTPreprocessorMacroExpansion getASTNode() {
		return (IASTPreprocessorMacroExpansion) mAstNode;
	}

}
