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
	private final SourceRewriter mRewriter;

	private CommaDeleter(final List<IPSTNode> childrenToDelete, final List<CommaSeparatedChild> allChildren,
			final SourceRewriter rewriter) {
		super(childrenToDelete, allChildren);
		this.mRewriter = rewriter;
	}

	@Override
	protected void deleteComma(final ISourceRange location) {
		if (mRewriter != null) {
			Change.replaceByWhitespace(mRewriter, location);
		}
	}

	@Override
	protected void deleteNode(final IPSTNode node) {
		if (mRewriter != null) {
			Change.deleteNodeText(mRewriter, node);
		}
	}
	
	static void deleteNodesWithComma(final SourceRewriter rewriter, final List<IPSTNode> nodesToDelete,
			final List<CommaSeparatedChild> commaPositions) {
		try {
			new CommaDeleter(nodesToDelete, commaPositions, rewriter).deleteChildren();
		} catch (final MissingCommaLocationException e) {
			throw new ChangeConflictException(e);
		}
	}

	static boolean isDeletionWithCommaPossible(final IPSTNode node, final List<CommaSeparatedChild> commaPositions) {
		try {
			new CommaDeleter(Arrays.asList(node), commaPositions, null).deleteChildren();
		} catch (final MissingCommaLocationException e) {
			return false;
		}
		return true;
	}
}
