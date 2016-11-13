package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by replacing.
 */
public class ReplaceChange extends Change {
	private final String mReplacement;
	
	ReplaceChange(final IPSTNode node, final String replacement) {
		super(node);
		mReplacement = replacement;
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		rewriter.replace(getNode(), mReplacement);
	}
	
	@Override
	public String toString() {
		return "Replace " + getNode() + " (by \"" + mReplacement + "\")";
	}
}
