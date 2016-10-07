package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChildDeleter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

final class CommaDeleter extends CommaSeparatedChildDeleter {
	private SourceRewriter rewriter;

	private CommaDeleter(List<IPSTNode> childrenToDelete, List<CommaSeparatedChild> allChildren,
			SourceRewriter rewriter) {
		super(childrenToDelete, allChildren);
		this.rewriter = rewriter;
	}
	
	static boolean isDeletionWithCommaPossible(IPSTNode node, List<CommaSeparatedChild> commaPositions) {
		try {
			new CommaDeleter(Arrays.asList(node), commaPositions, null).deleteChildren();
		} catch (MissingCommaLocationException e) {
			return false;
		}
		return true;
	}
	
	static void deleteNodesWithComma(SourceRewriter rewriter, List<IPSTNode> nodesToDelete,
			List<CommaSeparatedChild> commaPositions) {
		try {
			new CommaDeleter(nodesToDelete, commaPositions, rewriter).deleteChildren();
		} catch (MissingCommaLocationException e) {
			throw new ChangeConflictException(e);
		}
	}
	

	@Override
	protected void deleteComma(ISourceRange location) {
		if (rewriter != null) {
			Change.replaceByWhitespace(rewriter, location);
		}
	}

	@Override
	protected void deleteNode(IPSTNode node) {
		if (rewriter != null) {
			Change.deleteNodeText(rewriter, node);
		}
	}
}