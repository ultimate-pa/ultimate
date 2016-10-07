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
	private GapVisitor() {		
	}
	
	public static boolean invokeAccept(IPSTNode node, IPSTGapVisitor action) {
		return node.accept(new GapVisitorDecorator(action, node.offset()));
	}
}

class GapVisitorDecorator implements IPSTVisitor {
	private final IPSTGapVisitor delegate;
	private final Deque<IPSTConditionalBlock> conditionalBlockStack = new ArrayDeque<>();
	private int cursor = -1;

	public GapVisitorDecorator(IPSTGapVisitor delegate, int startOffset) {
		this.delegate = delegate;
		this.cursor = startOffset;
	}
	
	private boolean checkForGapUntil(int endOffset) {
		if (cursor < endOffset) {
			// Limit to active branch
			int gapEndOffset = endOffset;
			if (!conditionalBlockStack.isEmpty()) {
				ISourceRange activeBranch = conditionalBlockStack.peek().getActiveBranchLocation();
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
	
	private int afterVisit(IPSTNode node, int result) {			
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (result == PROCESS_SKIP) {
			cursor = Math.max(node.endOffset(), cursor);
			return PROCESS_SKIP;
		}
				
		if (node instanceof IPSTConditionalBlock) {
			conditionalBlockStack.push((IPSTConditionalBlock)node);
		} else if (node.getChildren().isEmpty()) {
			// No gap if this is a leaf node. CONTINUE is returned to get leave called
			cursor = Math.max(node.endOffset(), cursor);
		}
		
		return PROCESS_CONTINUE;
	}
	
	private int afterLeave(IPSTNode node, int result) {			
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (node instanceof IPSTConditionalBlock) {
			conditionalBlockStack.pop();
		}
		return PROCESS_CONTINUE;
	}
	
	@Override
	public int defaultVisit(IPSTNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, delegate.defaultVisit(node));
	}

	@Override
	public int defaultLeave(IPSTNode node) {
		if (checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.defaultLeave(node));
	}
	
	@Override
	public int visit(IPSTTranslationUnit node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTRegularNode node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTMacroExpansion node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTIncludeDirective node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTDirective node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTComment node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTConditionalBlock node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int visit(IPSTLiteralRegion node) {			
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}		
		return afterVisit(node, delegate.visit(node));
	}

	@Override
	public int leave(IPSTTranslationUnit node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTRegularNode node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTMacroExpansion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTIncludeDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTComment node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTConditionalBlock node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}

	@Override
	public int leave(IPSTLiteralRegion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, delegate.leave(node));
	}
}