package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceDocumentLocationPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

public class PSTACSLNode extends PSTNode implements IPSTACSLNode {

	private final ACSLNode mAcslNode;

	public PSTACSLNode(final ISourceDocument source, final ISourceRange location, final ACSLNode acslNode) {
		super(source, location, null);
		mAcslNode = acslNode;
	}

	@Override
	public ACSLNode getACSLNode() {
		return mAcslNode;
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
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(this.getClass().getSimpleName());
		final String acslNodeString = mAcslNode.toString();
		sb.append(" (");
		if (acslNodeString.length() > ASTNODE_TOSTRING_LIMIT) {
			sb.append(acslNodeString, 0, ASTNODE_TOSTRING_LIMIT).append("...");
		} else {
			sb.append(acslNodeString);
		}
		sb.append(")");
		sb.append(" [");
		SourceDocumentLocationPrinter.appendTo(mSource, mOffset, mEndOffset, sb);
		sb.append("]");
		return sb.toString();
	}
	
}
