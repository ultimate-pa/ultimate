package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTComment extends PSTNode implements IPSTComment {
	
	public PSTComment(ISourceDocument source, ISourceRange location, IASTComment comment) {
		super(source, location, comment);
	}

	@Override
	public IASTComment getASTNode() {
		return (IASTComment) astNode;
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
