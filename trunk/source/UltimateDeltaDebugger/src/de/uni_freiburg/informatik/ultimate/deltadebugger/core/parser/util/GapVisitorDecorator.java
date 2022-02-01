/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
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
 * Decorator for a PST visitor.
 */
class GapVisitorDecorator implements IPSTVisitor {
	private final IPSTGapVisitor mDelegate;
	private final Deque<IPSTConditionalBlock> mConditionalBlockStack = new ArrayDeque<>();
	private int mCursor = -1;
	
	public GapVisitorDecorator(final IPSTGapVisitor delegate, final int startOffset) {
		mDelegate = delegate;
		mCursor = startOffset;
	}
	
	int afterLeave(final IPSTNode node, final int result) {
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (node instanceof IPSTConditionalBlock) {
			mConditionalBlockStack.pop();
		}
		return PROCESS_CONTINUE;
	}
	
	int afterVisit(final IPSTNode node, final int result) {
		if (result == PROCESS_ABORT) {
			return PROCESS_ABORT;
		}
		if (result == PROCESS_SKIP) {
			mCursor = Math.max(node.endOffset(), mCursor);
			return PROCESS_SKIP;
		}
		
		if (node instanceof IPSTConditionalBlock) {
			mConditionalBlockStack.push((IPSTConditionalBlock) node);
		} else if (node.getChildren().isEmpty()) {
			// No gap if this is a leaf node. CONTINUE is returned to get leave called
			mCursor = Math.max(node.endOffset(), mCursor);
		}
		
		return PROCESS_CONTINUE;
	}
	
	boolean checkForGapUntil(final int endOffset) {
		if (mCursor < endOffset) {
			// Limit to active branch
			int gapEndOffset = endOffset;
			if (!mConditionalBlockStack.isEmpty()) {
				final ISourceRange activeBranch = mConditionalBlockStack.peek().getActiveBranchLocation();
				if (mCursor < activeBranch.offset()) {
					mCursor = activeBranch.offset();
				}
				if (gapEndOffset > activeBranch.endOffset()) {
					gapEndOffset = activeBranch.endOffset();
				}
			}
			
			if (mDelegate.visitGap(mCursor, gapEndOffset) == PROCESS_ABORT) {
				return false;
			}
			mCursor = endOffset;
		}
		return true;
	}
	
	@Override
	public int defaultLeave(final IPSTNode node) {
		if (checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.defaultLeave(node));
	}
	
	@Override
	public int defaultVisit(final IPSTNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.defaultVisit(node));
	}
	
	@Override
	public int leave(final IPSTComment node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTACSLComment node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTACSLNode node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTConditionalBlock node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTIncludeDirective node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTLiteralRegion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTMacroExpansion node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTRegularNode node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int leave(final IPSTTranslationUnit node) {
		if (!checkForGapUntil(node.endOffset())) {
			return PROCESS_ABORT;
		}
		return afterLeave(node, mDelegate.leave(node));
	}
	
	@Override
	public int visit(final IPSTComment node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTACSLComment node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTACSLNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTConditionalBlock node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTDirective node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTIncludeDirective node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTLiteralRegion node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTMacroExpansion node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTRegularNode node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
	
	@Override
	public int visit(final IPSTTranslationUnit node) {
		if (!checkForGapUntil(node.offset())) {
			return PROCESS_ABORT;
		}
		return afterVisit(node, mDelegate.visit(node));
	}
}
