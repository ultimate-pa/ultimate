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

public abstract class PSTNode implements IPSTNode {
	
	static final int ASTNODE_TOSTRING_LIMIT = 32;
	
	protected final int offset;
	protected final int endOffset;
	protected final IASTNode astNode;
	protected final ISourceDocument source;
	protected IPSTNode parent = null;
	protected List<IPSTNode> children = null;
	protected List<IASTNode> unexpandedChildNodes = null;
	
	public PSTNode(ISourceDocument source, ISourceRange location, IASTNode astNode) {
		this.source = Objects.requireNonNull(source);
		offset = location.offset();
		endOffset = location.endOffset();
		if (offset < 0 || offset > endOffset) {
			throw new IllegalArgumentException("malformed source range");
		}
		this.astNode = astNode;
	}

	@Override
	public final int offset() {
		return offset;
	}

	@Override
	public final int endOffset() {
		return endOffset;
	}

	@Override
	public final IPSTNode getParent() {
		return parent;
	}

	@Override
	public List<IPSTNode> getChildren() {
		return children != null ? children : Collections.emptyList();
	}

	@Override
	public IASTNode getASTNode() {
		return astNode;
	}

	@Override
	public List<IASTNode> getUnexpandedChildNodes() {
		return unexpandedChildNodes != null ? unexpandedChildNodes : Collections.emptyList();
	}

	@Override
	public IPSTTranslationUnit getTranslationUnit() {
		IPSTNode node = this;
		for (IPSTNode p = parent; p != null; p = p.getParent()) {
			node = p;
		}
		return node instanceof IPSTTranslationUnit ? (IPSTTranslationUnit) node : null;
	}

	@Override
	public ISourceDocument getSource() {
		return source;
	}
	
	@Override
	public String getSourceText() {
		return source.getText(offset, endOffset);
	}

	@Override
	public int getStartingLineNumber() {
		return source.getLineNumber(offset);
	}

	@Override
	public int getEndingLineNumber() {
		return source.getLineNumber(offset != endOffset ? endOffset - 1 : offset);
	}

	@Override
	public final boolean accept(IPSTVisitor action) {
		return acceptNonRecursive(this, action);
	}

	@Override
	public IPSTRegularNode getRegularParent() {
		for (IPSTNode p = parent; p != null; p = p.getParent()) {
			if (p instanceof IPSTRegularNode) {
				return (IPSTRegularNode)p;
			}
		}
		return null;
	}
	
	@Override
	public IPSTNode findDescendantByLocation(ISourceRange location) {
		// Possible improvement: This implementation does not take advantage of the 
		// ordering of child nodes and could use a binary search...
		final IPSTNode startNode = this;
		final PSTVisitorWithResult<IPSTNode> action = new PSTVisitorWithResult<IPSTNode>() {
			@Override
			public int defaultVisit(IPSTNode node) {
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
	public void setParent(IPSTNode node) {
		if (parent != null) {
			throw new IllegalStateException("Node already has parent");
		}
		parent = node;
	}

	@Override
	public void addChild(IPSTNode node) {
		addChild(children == null ? 0 : children.size(), node);
	}

	@Override
	public void addChild(int index, IPSTNode node) {
		if (index < 0 || index > ((children != null) ? children.size() : 0)) {
			throw new IndexOutOfBoundsException();
		}
		
		if (node.getParent() != null) {
			throw new IllegalStateException("node to be inserted already has a parent");
		}		

		if (children == null) {
			children = new ArrayList<>(2);
		}
		
		children.add(index, node);
		node.setParent(this);
	}

	@Override
	public void removeChild(int index) {
		if (children == null || index < 0 || index >= children.size()) {
			throw new IndexOutOfBoundsException();
		}
		children.remove(index).setParent(null);
	}

	@Override
	public void setUnexpandedChildNodes(List<IASTNode> astNodes) {
		unexpandedChildNodes = astNodes;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (astNode != null) {
			sb.append(astNode.getClass().getSimpleName());
			final String astNodeString = astNode.toString().replace("\n", "\\n").replace("\r", "");
			if (!astNodeString.startsWith("org.eclipse.cdt") ) {
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
		SourceDocumentLocationPrinter.appendTo(source, offset, endOffset, sb);
		sb.append("]");
		return sb.toString();
	}
	
	/*
	 * Non-recursive visitor implementation. Derived types implement
	 * dispatchVisit/dispatchLeave instead of accept to invoke the corresponding
	 * overload.
	 */
	abstract int dispatchVisit(IPSTVisitor action);
	abstract int dispatchLeave(IPSTVisitor action);
	
	
	private static class VisitorStep {
		PSTNode node;
		int state;
		VisitorStep tail;
		VisitorStep(PSTNode node) {
			this.node = node;
		}
	}
	
	protected static boolean acceptNonRecursive(PSTNode root, IPSTVisitor action) {
		VisitorStep head = new VisitorStep(root);
		while(head != null) {
			if (head.state == 0) {
				int res = head.node.dispatchVisit(action);
				if (res == IPSTVisitor.PROCESS_ABORT) {
					return false;
				} else if (res == IPSTVisitor.PROCESS_SKIP) {
					head = head.tail;
					continue;
				}
				head.state = 1;
			}
			
			if (head.node.children != null && head.state <= head.node.children.size()) {
				final IPSTNode nextChild = head.node.children.get(head.state - 1);
				++head.state;

				if (nextChild instanceof PSTNode) {
					VisitorStep nextStep = new VisitorStep((PSTNode) nextChild);
					nextStep.tail = head;
					head = nextStep;
					continue;
				}
				if (!nextChild.accept(action)) {
					return false;
				}
				continue;
			}
			
			if (head.node.dispatchLeave(action) == IPSTVisitor.PROCESS_ABORT) {
				return false;
			}
			
        	head = head.tail;
		}
		
		return true;
	}
}




