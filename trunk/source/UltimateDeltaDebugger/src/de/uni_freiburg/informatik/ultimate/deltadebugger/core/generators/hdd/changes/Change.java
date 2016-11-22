package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * A change to the C code.
 */
public abstract class Change implements IChangeHandle {
	private final IPSTNode mNode;
	
	private int mIndex = -1;
	
	/**
	 * @param node
	 *            PST node.
	 */
	public Change(final IPSTNode node) {
		mNode = node;
	}
	
	static void deleteNodeText(final SourceRewriter rewriter, final IPSTNode node) {
		rewriter.replace(node, RewriteUtils.getDeletionStringWithWhitespaces(node));
	}
	
	static void replaceByWhitespace(final SourceRewriter rewriter, final ISourceRange location) {
		rewriter.replace(location, " ");
	}
	
	/**
	 * Applies a change.
	 * 
	 * @param rewriter
	 *            source rewriter
	 */
	public abstract void apply(SourceRewriter rewriter);
	
	public IPSTNode getNode() {
		return mNode;
	}
	
	@Override
	public int getSequenceIndex() {
		return mIndex;
	}
	
	/**
	 * @return {@code true} iff this change has a deferred change.
	 */
	public boolean hasDeferredChange() {
		return false;
	}
	
	public void setSequenceIndex(final int index) {
		mIndex = index;
	}
	
	/**
	 * Updates the deferred change.
	 * 
	 * @param deferredChangeMap
	 *            map (PST node -> deferred change)
	 */
	public void updateDeferredChange(final Map<IPSTNode, Change> deferredChangeMap) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Creates an alternative change instance. Note that a new instance is required because the sequence index depends
	 * on the containing list.
	 * 
	 * @return an optional alternative to this change
	 */
	public Optional<Change> createAlternativeChange() {
		return Optional.empty();
	}
}
