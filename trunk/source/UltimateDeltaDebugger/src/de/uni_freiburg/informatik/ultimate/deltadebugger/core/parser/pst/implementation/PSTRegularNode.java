package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTRegularNode extends PSTNode implements IPSTRegularNode {

	public PSTRegularNode(ISourceDocument source, ISourceRange location, IASTNode astNode) {
		super(source, location, astNode);
	}

	@Override
	int dispatchVisit(IPSTVisitor action) {
		return action.visit(this);
	}
	
	@Override
	int dispatchLeave(IPSTVisitor action) {
		return action.leave(this);
	}

	@Override
	public IPSTRegularNode findRegularChild(IASTNode astNode) {
		final PSTVisitorWithResult<IPSTRegularNode> action = new PSTVisitorWithResult<IPSTRegularNode>() {
			@Override
			public int visit(IPSTRegularNode node) {
				if (PSTRegularNode.this == node) {
					return PROCESS_CONTINUE;
				} else if (node.getASTNode() == astNode) {
					setResult(node);
					return PROCESS_ABORT;
				}
				return PROCESS_SKIP;
			}
		};
		this.accept(action);
		return action.getResult().orElse(null);
	}
	
}
