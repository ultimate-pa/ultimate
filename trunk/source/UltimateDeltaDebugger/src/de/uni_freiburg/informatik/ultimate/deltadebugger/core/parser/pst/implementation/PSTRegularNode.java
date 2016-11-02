package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTRegularNode extends PSTNode implements IPSTRegularNode {

	public PSTRegularNode(final ISourceDocument source, final ISourceRange location, final IASTNode astNode) {
		super(source, location, astNode);
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
	public IPSTRegularNode findRegularChild(final IASTNode astNode) {
		final PSTVisitorWithResult<IPSTRegularNode> action = new PSTVisitorWithResult<IPSTRegularNode>() {
			@Override
			public int visit(final IPSTRegularNode node) {
				if (PSTRegularNode.this.equals(node)) {
					return PROCESS_CONTINUE;
				} else if (node.getASTNode() == astNode) {
					setResult(node);
					return PROCESS_ABORT;
				}
				return PROCESS_SKIP;
			}
		};
		accept(action);
		return action.getResult().orElse(null);
	}

}
