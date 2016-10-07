package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTIncludeDirective extends PSTDirective implements IPSTIncludeDirective {
	
	public PSTIncludeDirective(ISourceDocument source, ISourceRange location, IASTPreprocessorIncludeStatement include) {
		super(source, location, include);
	}

	@Override
	public IASTPreprocessorIncludeStatement getASTNode() {
		return (IASTPreprocessorIncludeStatement) astNode;
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
