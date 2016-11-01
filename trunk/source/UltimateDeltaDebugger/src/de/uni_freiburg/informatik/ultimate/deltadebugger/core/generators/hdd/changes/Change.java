package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public abstract class Change implements IChangeHandle {
	static void deleteNodeText(final SourceRewriter rewriter, final IPSTNode node) {
		rewriter.replace(node, RewriteUtils.getDeletionStringWithWhitespaces(node));
	}

	static void replaceByWhitespace(final SourceRewriter rewriter, final ISourceRange location) {
		rewriter.replace(location, " ");
	}

	private final IPSTNode node;

	private int index = -1;

	public Change(final IPSTNode node) {
		this.node = node;
	}

	public abstract void apply(SourceRewriter rewriter);

	public IPSTNode getNode() {
		return node;
	}

	@Override
	public int getSequenceIndex() {
		return index;
	}

	public boolean hasDeferredChange() {
		return false;
	}

	void setIndex(final int index) {
		this.index = index;
	}

	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		throw new UnsupportedOperationException();
	}
}