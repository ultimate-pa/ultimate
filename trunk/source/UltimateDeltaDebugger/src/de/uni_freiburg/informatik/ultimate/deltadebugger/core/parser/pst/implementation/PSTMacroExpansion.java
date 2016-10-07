package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTMacroExpansion extends PSTNode implements IPSTMacroExpansion {
	
	public PSTMacroExpansion(ISourceDocument source, ISourceRange location, IASTPreprocessorMacroExpansion expansion) {
		super(source, location, expansion);
	}

	@Override
	public IASTPreprocessorMacroExpansion getASTNode() {
		return (IASTPreprocessorMacroExpansion) astNode;
	}
	
	@Override
	int dispatchVisit(IPSTVisitor action) {
		return action.visit(this);
	}
	
	@Override
	int dispatchLeave(IPSTVisitor action) {
		return action.leave(this);
	}
	
}
