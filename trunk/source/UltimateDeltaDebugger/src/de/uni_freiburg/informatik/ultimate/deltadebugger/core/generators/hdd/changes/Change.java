package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public abstract class Change implements ChangeHandle {
	private final IPSTNode node;
	private int index = -1;
	
	public Change(IPSTNode node) {
		this.node = node;
	}
	
	public IPSTNode getNode() {
		return node;
	}
	
	public abstract void apply(SourceRewriter rewriter);
	
	public boolean hasDeferredChange() {
		return false;
	}
	
	public void updateDeferredChange(Map<IPSTNode, Change> deferredChangeMap) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public int getSequenceIndex() {
		return index;
	}
	
	void setIndex(int index) {
		this.index = index;
	}
	
	static void replaceByWhitespace(SourceRewriter rewriter, ISourceRange location) {
		rewriter.replace(location, " ");
	}
	
	static void deleteNodeText(SourceRewriter rewriter, IPSTNode node) {
		rewriter.replace(node, RewriteUtils.getDeletionStringWithWhitespaces(node));
	}
}