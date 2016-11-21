package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTComment;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceDocumentLocationPrinter;

public class PSTACSLComment extends PSTComment implements IPSTACSLComment {

	public PSTACSLComment(final ISourceDocument source, final ISourceRange location, final IASTComment comment) {
		super(source, location, comment);
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
		final String text = getSourceText().replace("\n", "\\n").replace("\r", "");
		final StringBuilder sb = new StringBuilder();
		sb.append(this.getClass().getSimpleName());
		sb.append(" (");
		if (text.length() > ASTNODE_TOSTRING_LIMIT) {
			sb.append(text, 0, ASTNODE_TOSTRING_LIMIT).append("...");
		} else {
			sb.append(text);
		}
		sb.append(")");
		sb.append(" [");
		SourceDocumentLocationPrinter.appendTo(mSource, mOffset, mEndOffset, sb);
		sb.append("]");
		return sb.toString();
	}
}
