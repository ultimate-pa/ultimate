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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceDocumentLocationPrinter;

/**
 * Abstract PST node.
 */
public abstract class PSTNode implements IPSTNode {
	protected static final int ASTNODE_TOSTRING_LIMIT = 32;
	
	protected final int mOffset;
	protected final int mEndOffset;
	protected final IASTNode mAstNode;
	protected final ISourceDocument mSource;
	protected IPSTNode mParent;
	protected List<IPSTNode> mChildren;
	protected List<IASTNode> mUnexpandedChildNodes;
	
	/**
	 * @param source
	 *            Source document.
	 * @param location
	 *            source range
	 * @param astNode
	 *            AST node
	 */
	public PSTNode(final ISourceDocument source, final ISourceRange location, final IASTNode astNode) {
		mSource = Objects.requireNonNull(source);
		mOffset = location.offset();
		mEndOffset = location.endOffset();
		if (mOffset < 0 || mOffset > mEndOffset) {
			throw new IllegalArgumentException("malformed source range");
		}
		mAstNode = astNode;
	}
	
	@Override
	public final boolean accept(final IPSTVisitor action) {
		return acceptNonRecursive(this, action);
	}
	
	@Override
	public void addChild(final int index, final IPSTNode node) {
		if (index < 0 || index > (mChildren != null ? mChildren.size() : 0)) {
			throw new IndexOutOfBoundsException();
		}
		
		if (node.getParent() != null) {
			throw new IllegalStateException("node to be inserted already has a parent");
		}
		
		if (mChildren == null) {
			mChildren = new ArrayList<>(2);
		}
		
		mChildren.add(index, node);
		node.setParent(this);
	}
	
	@Override
	public void addChild(final IPSTNode node) {
		addChild(mChildren == null ? 0 : mChildren.size(), node);
	}
	
	abstract int dispatchLeave(IPSTVisitor action);
	
	/*
	 * Non-recursive visitor implementation. Derived types implement dispatchVisit/dispatchLeave instead of accept to
	 * invoke the corresponding overload.
	 */
	abstract int dispatchVisit(IPSTVisitor action);
	
	@Override
	public final int endOffset() {
		return mEndOffset;
	}
	
	@SuppressWarnings("squid:S1698")
	@Override
	public IPSTNode findDescendantByLocation(final ISourceRange location) {
		// Possible improvement: This implementation does not take advantage of the
		// ordering of child nodes and could use a binary search...
		final IPSTNode startNode = this;
		final PSTVisitorWithResult<IPSTNode> action = new PSTVisitorWithResult<IPSTNode>() {
			@Override
			public int defaultVisit(final IPSTNode node) {
				if (node.equalsSourceRange(location) && startNode != node) {
					setResult(node);
					return PROCESS_ABORT;
				}
				return node.contains(location) ? PROCESS_CONTINUE : PROCESS_SKIP;
			}
		};
		startNode.accept(action);
		return action.getResult().orElse(null);
	}
	
	@Override
	public IASTNode getAstNode() {
		return mAstNode;
	}
	
	@Override
	public List<IPSTNode> getChildren() {
		return mChildren != null ? mChildren : Collections.emptyList();
	}
	
	@Override
	public int getEndingLineNumber() {
		return mSource.getLineNumber(mOffset != mEndOffset ? (mEndOffset - 1) : mOffset);
	}
	
	@Override
	public final IPSTNode getParent() {
		return mParent;
	}
	
	@Override
	public IPSTRegularNode getRegularParent() {
		for (IPSTNode p = mParent; p != null; p = p.getParent()) {
			if (p instanceof IPSTRegularNode) {
				return (IPSTRegularNode) p;
			}
		}
		return null;
	}
	
	@Override
	public ISourceDocument getSource() {
		return mSource;
	}
	
	@Override
	public String getSourceText() {
		return mSource.getText(mOffset, mEndOffset);
	}
	
	@Override
	public int getStartingLineNumber() {
		return mSource.getLineNumber(mOffset);
	}
	
	@Override
	public IPSTTranslationUnit getTranslationUnit() {
		IPSTNode node = this;
		for (IPSTNode p = mParent; p != null; p = p.getParent()) {
			node = p;
		}
		return node instanceof IPSTTranslationUnit ? (IPSTTranslationUnit) node : null;
	}
	
	@Override
	public List<IASTNode> getUnexpandedChildNodes() {
		return mUnexpandedChildNodes != null ? mUnexpandedChildNodes : Collections.emptyList();
	}
	
	@Override
	public final int offset() {
		return mOffset;
	}
	
	@Override
	public void removeChild(final int index) {
		if (mChildren == null || index < 0 || index >= mChildren.size()) {
			throw new IndexOutOfBoundsException();
		}
		mChildren.remove(index).setParent(null);
	}
	
	@Override
	public void setParent(final IPSTNode node) {
		if (mParent != null) {
			throw new IllegalStateException("Node already has parent");
		}
		mParent = node;
	}
	
	@Override
	public void setUnexpandedChildNodes(final List<IASTNode> astNodes) {
		mUnexpandedChildNodes = astNodes;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mAstNode != null) {
			sb.append(mAstNode.getClass().getSimpleName());
			final String astNodeString = mAstNode.toString().replace("\n", "\\n").replace("\r", "");
			if (!astNodeString.startsWith("org.eclipse.cdt")) {
				sb.append(" (");
				if (astNodeString.length() > ASTNODE_TOSTRING_LIMIT) {
					sb.append(astNodeString, 0, ASTNODE_TOSTRING_LIMIT).append("...");
				} else {
					sb.append(astNodeString);
				}
				sb.append(")");
			}
		} else {
			sb.append(this.getClass().getSimpleName());
		}
		sb.append(" [");
		SourceDocumentLocationPrinter.appendTo(mSource, mOffset, mEndOffset, sb);
		sb.append("]");
		return sb.toString();
	}
	
	protected static boolean acceptNonRecursive(final PSTNode root, final IPSTVisitor action) {
		VisitorStep head = new VisitorStep(root);
		while (head != null) {
			if (head.mState == 0) {
				final int res = head.mNode.dispatchVisit(action);
				if (res == IPSTVisitor.PROCESS_ABORT) {
					return false;
				} else if (res == IPSTVisitor.PROCESS_SKIP) {
					head = head.mTail;
					continue;
				}
				head.mState = 1;
			}
			
			if (head.mNode.mChildren != null && head.mState <= head.mNode.mChildren.size()) {
				final IPSTNode nextChild = head.mNode.mChildren.get(head.mState - 1);
				++head.mState;
				
				if (nextChild instanceof PSTNode) {
					final VisitorStep nextStep = new VisitorStep((PSTNode) nextChild);
					nextStep.mTail = head;
					head = nextStep;
					continue;
				}
				if (!nextChild.accept(action)) {
					return false;
				}
				continue;
			}
			
			if (head.mNode.dispatchLeave(action) == IPSTVisitor.PROCESS_ABORT) {
				return false;
			}
			
			head = head.mTail;
		}
		
		return true;
	}
	
	/**
	 * A step in the visitor.
	 */
	private static class VisitorStep {
		private final PSTNode mNode;
		private int mState;
		private VisitorStep mTail;
		
		VisitorStep(final PSTNode node) {
			mNode = node;
		}
	}
}
