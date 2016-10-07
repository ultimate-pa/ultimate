package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTGapVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Utility class to invoke an IPSTGapVisitor on a given node
 */
public class GapVisitor {
	public static boolean invokeAccept(final IPSTNode node, final IPSTGapVisitor action) {
		return node.accept(new GapVisitorDecorator(action, node.offset()));
	}

	private GapVisitor() {
	}
}

class GapVisitorDecorator implements IPSTVisitor {
	private final IPSTGapVisitor delegate;
	private final Deque<IPSTConditionalBlock> conditionalBlockStack = new ArrayDeque<>();
	private int cursor = -1;

	public GapVisitorDecorator(final IPSTGapVisitor delegate, final int startOffset) {
		this.delegate = delegate;
		cursor = startOffset;
	}

	private int afterLeave(final IPSTNode node, final int result) {
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (node instanceof IPSTConditionalBlock) {
			conditionalBlockStack.pop();
		}
		return PROCESS_CONTINUE;
	}

	private int afterVisit(final IPSTNode node, final int result) {
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (result == PROCESS_SKIP) {
			cursor = Math.max(node.endOffset(), cursor);
			return PROCESS_SKIP;
		}

		if (node instanceof IPSTConditionalBlock) {
			conditionalBlockStack.push((IPSTConditionalBlock) node);
		} else if (node.getChildren().isEmpty()) {
			// No gap if this is a leaf node. CONTINUE is returned to get leave called
			cursor = Math.max(node.endOffset(), cursor);
		}

		return PROCESS_CONTINUE;
	}

	private boolean checkForGapUntil(final int endOffset) {
		if (cursor < endOffset) {
			// Limit to active branch
			int gapEndOffset = endOffset;
			if (!conditionalBlockStack.isEmpty()) {
				final ISourceRange activeBranch = conditionalBlockStack.peek().getActiveBranchLocation();
				if (cursor < activeBranch.offset()) {
					cursor = activeBranch.offset();
				}
				if (gapEndOffset > activeBranch.endOffset()) {
					gapEndOffset = activeBranch.endOffset();
				}
			}

			if (delegate.visitGap(cursor, gapEndOffset) == PROCESS_ABORT) {
				return false;
			}
			cursor = endOffset;
		}
		return true;
	}

	@Override
	public int defaultLeave(final IPSTNode node) {
		if (checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.defaultLeave(node));
	}

	@Override
	public int defaultVisit(final IPSTNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.defaultVisit(node));
	}

	@Override
	public int leave(final IPSTComment node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTConditionalBlock node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTIncludeDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTLiteralRegion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTMacroExpansion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTRegularNode node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(final IPSTTranslationUnit node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int visit(final IPSTComment node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTConditionalBlock node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTDirective node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTIncludeDirective node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTLiteralRegion node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTMacroExpansion node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTRegularNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(final IPSTTranslationUnit node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.visit(node));
	}
}